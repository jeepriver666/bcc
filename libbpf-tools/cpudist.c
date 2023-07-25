// SPDX-License-Identifier: (LGPL-2.1 OR BSD-2-Clause)
// Copyright (c) 2020 Wenbo Zhang
//
// Based on cpudist(8) from BCC by Brendan Gregg & Dina Goldshtein.
// 8-May-2020   Wenbo Zhang   Created this.
#include <argp.h>
#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>
#include <bpf/libbpf.h>
#include <bpf/bpf.h>
#include "cpudist.h"
#include "cpudist.skel.h"
#include "trace_helpers.h"

// 参数配置结构体，具体含义如 opts 结构体数组里的解释
static struct env {
	time_t interval;
	pid_t pid;
	char *cgroupspath;
	bool cg;
	int times;
	bool offcpu;
	bool timestamp;
	bool per_process;
	bool per_thread;
	bool milliseconds;
	bool verbose;
} env = {
	.interval = 99999999,
	.pid = -1,
	.times = 99999999,
};

static volatile bool exiting;

const char *argp_program_version = "cpudist 0.1";
const char *argp_program_bug_address =
	"https://github.com/iovisor/bcc/tree/master/libbpf-tools";
const char argp_program_doc[] =
"Summarize on-CPU time per task as a histogram.\n"
"\n"
"USAGE: cpudist [--help] [-O] [-T] [-m] [-P] [-L] [-p PID] [interval] [count] [-c CG]\n"
"\n"
"EXAMPLES:\n"
"    cpudist              # summarize on-CPU time as a histogram"
"    cpudist -O           # summarize off-CPU time as a histogram"
"    cpudist -c CG        # Trace process under cgroupsPath CG\n"
"    cpudist 1 10         # print 1 second summaries, 10 times"
"    cpudist -mT 1        # 1s summaries, milliseconds, and timestamps"
"    cpudist -P           # show each PID separately"
"    cpudist -p 185       # trace PID 185 only";

static const struct argp_option opts[] = {
	{ "offcpu", 'O', NULL, 0, "Measure off-CPU time" },
	{ "timestamp", 'T', NULL, 0, "Include timestamp on output" },
	{ "milliseconds", 'm', NULL, 0, "Millisecond histogram" },
	{ "cgroup", 'c', "/sys/fs/cgroup/unified", 0, "Trace process in cgroup path" },
	{ "pids", 'P', NULL, 0, "Print a histogram per process ID" },
	{ "tids", 'L', NULL, 0, "Print a histogram per thread ID" },
	{ "pid", 'p', "PID", 0, "Trace this PID only" },
	{ "verbose", 'v', NULL, 0, "Verbose debug output" },
	{ NULL, 'h', NULL, OPTION_HIDDEN, "Show the full help" },
	{},
};

// 函数作用： 解析命令行参数
// 参数1：key，参数选项
// 参数2：arg，参数值
// 参数3：state，结构体指针，包含关于参数解析器内部状态的信息
static error_t parse_arg(int key, char *arg, struct argp_state *state)
{
	// 用于跟踪在解析过程中遇到的位置参数数量
	static int pos_args;

	switch (key) {
	case 'h':
		// 显示帮助信息
		argp_state_help(state, stderr, ARGP_HELP_STD_HELP);
		break;
	case 'v':
		// env结构中的调试输出标志，设置为true
		env.verbose = true;
		break;
	case 'm':
		// 毫秒直方图标志，设置为true
		env.milliseconds = true;
		break;
	case 'c':
		// cgroupspath 不懂作用是啥
		env.cgroupspath = arg;
		env.cg = true;
		break;
	case 'p':
		errno = 0;
		// strtol函数把参数 arg 字符串转换为 10 的整型
		env.pid = strtol(arg, NULL, 10);
		if (errno) {
			fprintf(stderr, "invalid PID: %s\n", arg);
			argp_usage(state);
		}
		break;
	case 'O':
		env.offcpu = true;
		break;
	case 'P':
		env.per_process = true;
		break;
	case 'L':
		env.per_thread = true;
		break;
	case 'T':
		env.timestamp = true;
		break;
	case ARGP_KEY_ARG:
		errno = 0;
		if (pos_args == 0) {
			env.interval = strtol(arg, NULL, 10);
			if (errno) {
				fprintf(stderr, "invalid internal\n");
				argp_usage(state);
			}
		} else if (pos_args == 1) {
			env.times = strtol(arg, NULL, 10);
			if (errno) {
				fprintf(stderr, "invalid times\n");
				argp_usage(state);
			}
		} else {
			fprintf(stderr,
				"unrecognized positional argument: %s\n", arg);
			argp_usage(state);
		}
		pos_args++;
		break;
	default:
		return ARGP_ERR_UNKNOWN;
	}
	return 0;
}

// 打印等级函数，输出调试信息
static int libbpf_print_fn(enum libbpf_print_level level, const char *format, va_list args)
{
	if (level == LIBBPF_DEBUG && !env.verbose)
		return 0;
	return vfprintf(stderr, format, args);
}

// 获取最大 pid 值
static int get_pid_max(void)
{
	int pid_max;
	FILE *f;

	f = fopen("/proc/sys/kernel/pid_max", "r");
	if (!f)
		return -1;
	if (fscanf(f, "%d\n", &pid_max) != 1)
		pid_max = -1;
	fclose(f);
	return pid_max;
}

// 信号处理回调函数，控制全局变量 exiting ，用于退出 main 函数
static void sig_handler(int sig)
{
	exiting = true;
}

// 打印日志直方图，参数 fd 表示BPF Map的文件描述符
static int print_log2_hists(int fd)
{
	// 根据全局变量值选择 直方图的输出时间单位，毫秒还是微妙
	char *units = env.milliseconds ? "msecs" : "usecs";
	__u32 lookup_key = -2, next_key;

	// 自定义结构体 hist，用于存储日志直方图的数据
	struct hist hist;
	int err;

	// bpf_map_get_next_key 函数用于获取下一个键值对的键，并将其保存在 next_key 中。
	// 它返回true表示成功获取下一个键值对的键，false表示已经到达BPF Map的末尾。
	while (!bpf_map_get_next_key(fd, &lookup_key, &next_key)) {
		// 使用 bpf_map_lookup_elem 函数查找BPF Map中与键 next_key 相关联的值，并将其保存在 hist 变量中
		err = bpf_map_lookup_elem(fd, &next_key, &hist);
		if (err < 0) {
			fprintf(stderr, "failed to lookup hist: %d\n", err);
			return -1;
		}
		if (env.per_process)
			printf("\npid = %d %s\n", next_key, hist.comm);
		if (env.per_thread)
			printf("\ntid = %d %s\n", next_key, hist.comm);
		// 调用 print_log2_hist 函数打印日志直方图的槽位数据
		print_log2_hist(hist.slots, MAX_SLOTS, units);
		// 将 lookup_key 更新为 next_key，以便在下一次循环中继续从下一个键开始查找
		lookup_key = next_key;
	}

	lookup_key = -2;
	// 再次遍历BPF Map并删除已打印的键值对，以清理数据
	while (!bpf_map_get_next_key(fd, &lookup_key, &next_key)) {
		err = bpf_map_delete_elem(fd, &next_key);
		if (err < 0) {
			fprintf(stderr, "failed to cleanup hist : %d\n", err);
			return -1;
		}
		lookup_key = next_key;
	}
	return 0;
}

int main(int argc, char **argv)
{
	static const struct argp argp = {
		.options = opts,
		.parser = parse_arg,
		.doc = argp_program_doc,
	};
	struct cpudist_bpf *obj;
	int pid_max, fd, err;
	struct tm *tm;
	char ts[32];
	time_t t;
	int idx, cg_map_fd;
	int cgfd = -1;

	err = argp_parse(&argp, argc, argv, 0, NULL, NULL);
	if (err)
		return err;

	libbpf_set_print(libbpf_print_fn);

	obj = cpudist_bpf__open();
	if (!obj) {
		fprintf(stderr, "failed to open BPF object\n");
		return 1;
	}

	if (probe_tp_btf("sched_switch"))
		bpf_program__set_autoload(obj->progs.sched_switch_tp, false);
	else
		bpf_program__set_autoload(obj->progs.sched_switch_btf, false);

	/* initialize global data (filtering options) */
	obj->rodata->filter_cg = env.cg;
	obj->rodata->targ_per_process = env.per_process;
	obj->rodata->targ_per_thread = env.per_thread;
	obj->rodata->targ_ms = env.milliseconds;
	obj->rodata->targ_offcpu = env.offcpu;
	obj->rodata->targ_tgid = env.pid;

	pid_max = get_pid_max();
	if (pid_max < 0) {
		fprintf(stderr, "failed to get pid_max\n");
		return 1;
	}

	bpf_map__set_max_entries(obj->maps.start, pid_max);
	if (!env.per_process && !env.per_thread)
		bpf_map__set_max_entries(obj->maps.hists, 1);
	else
		bpf_map__set_max_entries(obj->maps.hists, pid_max);

	err = cpudist_bpf__load(obj);
	if (err) {
		fprintf(stderr, "failed to load BPF object: %d\n", err);
		goto cleanup;
	}

	/* update cgroup path fd to map */
	if (env.cg) {
		idx = 0;
		cg_map_fd = bpf_map__fd(obj->maps.cgroup_map);
		cgfd = open(env.cgroupspath, O_RDONLY);
		if (cgfd < 0) {
			fprintf(stderr, "Failed opening Cgroup path: %s", env.cgroupspath);
			goto cleanup;
		}
		if (bpf_map_update_elem(cg_map_fd, &idx, &cgfd, BPF_ANY)) {
			fprintf(stderr, "Failed adding target cgroup to map");
			goto cleanup;
		}
	}

	err = cpudist_bpf__attach(obj);
	if (err) {
		fprintf(stderr, "failed to attach BPF programs\n");
		goto cleanup;
	}

	fd = bpf_map__fd(obj->maps.hists);

	signal(SIGINT, sig_handler);

	printf("Tracing %s-CPU time... Hit Ctrl-C to end.\n", env.offcpu ? "off" : "on");

	/* main: poll */
	while (1) {
		sleep(env.interval);
		printf("\n");

		if (env.timestamp) {
			time(&t);
			tm = localtime(&t);
			strftime(ts, sizeof(ts), "%H:%M:%S", tm);
			printf("%-8s\n", ts);
		}

		err = print_log2_hists(fd);
		if (err)
			break;

		if (exiting || --env.times == 0)
			break;
	}

cleanup:
	cpudist_bpf__destroy(obj);
	if (cgfd > 0)
		close(cgfd);

	return err != 0;
}
