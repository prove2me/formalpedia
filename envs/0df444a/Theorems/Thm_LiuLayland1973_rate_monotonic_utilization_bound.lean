-- Prove2me | Theorems.Thm_LiuLayland1973_rate_monotonic_utilization_bound
-- name    : LiuLayland1973.rate_monotonic_utilization_bound
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:38:16.459268+00:00
-- url     : https://prove2.me/theorems/c576cd65-73e6-486e-97e0-53124798f4c5
-- title:
--   Liu–Layland bound: rate-monotonic scheduling meets every deadline if $\sum_i C_i/T_i \le n(2^{1/n}-1)$
-- statement:
--   This is the Liu–Layland schedulability test for *rate-monotonic* scheduling of periodic tasks on one processor, stated in discrete time with integer parameters.
--
--   Consider $n$ periodic tasks $\tau_1, \dots, \tau_n$. Task $\tau_i$ has an integer run time $C_i \ge 1$ and an integer period $T_i \ge C_i$. Its $k$-th job ($k = 0, 1, 2, \dots$) is released at time $kT_i$, needs $C_i$ units of processing, and has deadline $(k+1)T_i$, the release time of the next job of the same task. In particular all tasks release their first job at time $0$ (synchronous release). Time is divided into unit slots $[t, t+1)$, $t = 0, 1, 2, \dots$; in each slot the processor executes one unit of work of one task, or idles.
--
--   The *rate-monotonic* (RM) schedule is the preemptive fixed-priority schedule in which a task with a shorter period has higher priority, ties between equal periods being broken by the index of the task. In every slot $t$ the processor runs the highest-priority task that has released work not yet executed, and it idles only when no task has pending work; the jobs of one task are served in order of release. If the processor utilization of the task set satisfies
--
--   $$
--   U = \sum_{i=1}^{n} \frac{C_i}{T_i} \le n\left(2^{1/n} - 1\right),
--   $$
--
--   then every job of every task completes by its deadline under the RM schedule. Equivalently, for every task $\tau_i$ and every $k \ge 0$, task $\tau_i$ is executed in at least $(k+1)C_i$ of the slots before time $(k+1)T_i$.
--
--   The bound $n(2^{1/n} - 1)$ equals $1$ for $n = 1$, about $0.828$ for $n = 2$, and decreases to $\ln 2 \approx 0.693$ as $n \to \infty$, so every periodic task set that uses at most $\ln 2$ of the processor is schedulable by the rate-monotonic rule, whatever its periods. It is the classical sufficient schedulability test of fixed-priority real-time scheduling. Liu and Layland also showed that the bound cannot be improved: for every $n$ there are task sets that miss a deadline under rate-monotonic scheduling and whose utilization is arbitrarily close to $n(2^{1/n} - 1)$. That tightness statement is not part of this theorem.
--
--   **Formalization Note** Tasks are indexed by `Fin n`, that is by $0, \dots, n-1$ instead of $1, \dots, n$, and the parameters are `C T : Fin n → ℕ`. The schedule is a function `σ : ℕ → Option (Fin n)`, where `σ t = some i` means that task $i$ runs in slot $t$ and `σ t = none` means idling. The work of task $i$ released by time $t$ is $C_i$ times the number of $k$ with $kT_i \le t$, its service by time $t$ is the number of slots $s < t$ with `σ s = some i`, and the task has pending work at $t$ when its service is below its released work. The hypothesis `hσ` states that `σ t = some i` exactly when task $i$ has pending work at $t$ and no task of higher priority (smaller period, or equal period and smaller index) does. This determines `σ` uniquely by recursion on $t$, and such a schedule exists. Each task's work is served as one first-come-first-served backlog, which agrees with the job-by-job schedule up to the first missed deadline, so the conclusion is equivalent to the statement that no job misses its deadline. The utilization bound uses the real power $2^{1/n}$ (`Real.rpow`). With integer run times and periods, the continuous-time preemptive rate-monotonic schedule of Liu and Layland changes the running task only at integer times, so it coincides with the slot schedule above, and the theorem is the integer-parameter case of their result.
-- source:
--   C. L. Liu and J. W. Layland, Scheduling algorithms for multiprogramming in a hard-real-time environment, J. ACM 20(1) (1973), 46-61, Theorem 5 (for a set of m tasks with fixed priority order, the least upper bound to the processor utilization factor is U = m(2^{1/m}-1); the bound is computed for the rate-monotonic priority assignment, which is optimal among fixed-priority assignments by Theorem 2); complete proof in R. Devillers and J. Goossens, Liu and Layland's schedulability test revisited, Inform. Process. Lett. 73 (2000), 157-161; textbook statement: G. C. Buttazzo, Hard Real-Time Computing Systems, 3rd ed., Springer (2011), Section 4.3 (Rate Monotonic scheduling: a set of n periodic tasks is schedulable by RM if U <= n(2^{1/n}-1)).

import Mathlib

namespace LiuLayland1973

/-- Liu–Layland utilization bound for rate-monotonic scheduling (Liu–Layland 1973, Theorem 5),
in discrete time with integer parameters.

Tasks are `Fin n`; task `i` has run time `C i` and period `T i`, and releases its `k`-th job
(`k = 0, 1, 2, …`) at time `k * T i` with deadline `(k + 1) * T i` (all tasks release their
first job at time `0`). Time is divided into unit slots `[t, t + 1)`, `t : ℕ`; `σ t = some i`
means task `i` runs in slot `t` and `σ t = none` means the processor idles.

* `(Finset.range t).filter (σ · = some i)` are the slots before `t` given to task `i`
  (its cumulative service by time `t`);
* `(Finset.range (t + 1)).filter (fun k => k * T i ≤ t)` are the jobs of task `i` released by
  time `t`, so `C i * card` is the work it has released by time `t`;
* task `i` has pending work at `t` iff its service is below its released work;
* task `j` has higher rate-monotonic priority than task `i` iff `T j < T i`, or `T j = T i`
  and `j < i`.

`hσ` says that in every slot the processor runs the highest-priority task with pending work
(idling only if none has), which determines `σ` uniquely by recursion on `t`. Within a task,
work is served first-come first-served, so job `k` of task `i` is complete by its deadline iff
task `i` has received `(k + 1) * C i` units of service by time `(k + 1) * T i`. -/
theorem rate_monotonic_utilization_bound (n : ℕ) (C T : Fin n → ℕ)
    (hC : ∀ i, 1 ≤ C i) (hCT : ∀ i, C i ≤ T i)
    (hU : ∑ i, (C i : ℝ) / (T i : ℝ) ≤ (n : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) - 1))
    (σ : ℕ → Option (Fin n))
    (hσ : ∀ (t : ℕ) (i : Fin n), σ t = some i ↔
      (((Finset.range t).filter (fun s => σ s = some i)).card <
          C i * ((Finset.range (t + 1)).filter (fun k => k * T i ≤ t)).card) ∧
      ∀ j : Fin n, (T j < T i ∨ (T j = T i ∧ j < i)) →
        C j * ((Finset.range (t + 1)).filter (fun k => k * T j ≤ t)).card ≤
          ((Finset.range t).filter (fun s => σ s = some j)).card)
    (i : Fin n) (k : ℕ) :
    (k + 1) * C i ≤
      ((Finset.range ((k + 1) * T i)).filter (fun s => σ s = some i)).card := by
  sorry

end LiuLayland1973
