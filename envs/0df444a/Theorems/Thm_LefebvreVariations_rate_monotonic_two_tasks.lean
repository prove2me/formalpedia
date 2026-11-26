-- Prove2me | Theorems.Thm_LefebvreVariations_rate_monotonic_two_tasks
-- name    : LefebvreVariations.rate_monotonic_two_tasks
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:36:08.251083+00:00
-- url     : https://prove2.me/theorems/391f2b9a-8f73-4448-b2e7-228bda174961
-- title:
--   Lefebvre's variations, No. 224 — on a theme by Liu and Layland: rate-monotonic scheduling of two tasks meets every deadline when the utilization is at most 2(√2 − 1)
-- statement:
--   Let $C_0,C_1,T_0,T_1$ be positive integers with $C_i\le T_i$ and
--   $$
--   \frac{C_0}{T_0}+\frac{C_1}{T_1}\ \le\ 2\left(\sqrt2-1\right).
--   $$
--   Then in the rate-monotonic schedule of the two periodic tasks, every job meets its deadline:
--   $$
--   \#\{\,s<(k+1)T_i : \text{task } i \text{ runs in slot } s\,\}\ \ge\ (k+1)\,C_i\qquad\text{for all } i\in\{0,1\},\ k\ge 0 .
--   $$
--
--   This is the case $n=2$ of the Liu–Layland utilization bound $n\,(2^{1/n}-1)$, which the platform lists as open for every $n$. It is the first size where the bound is not simply the condition that the utilization be at most $1$.
--
--   Time is divided into unit slots. Task $i$ releases its $k$-th job at time $kT_i$, with deadline $(k+1)T_i$ and $C_i$ slots of work; in every slot the processor runs the pending task with the shortest period (ties broken by the smaller index), or idles if none is pending. This is the rate-monotonic schedule of Liu and Layland in discrete time.
--
--   **Formalization Note** The tasks are `Fin 2`, with `C T : Fin 2 → ℕ`, `1 ≤ C i ≤ T i`. The schedule `σ : ℕ → Option (Fin 2)` is characterised by the hypothesis `hσ`: `σ t = some i` iff task `i` has pending work at `t` (its service so far is below `C i` times the number of jobs released by `t`, which is `⌊t / T i⌋ + 1`) and no higher-priority task has pending work. This determines `σ` uniquely by recursion on `t`. The conclusion says that by time `(k + 1) * T i` task `i` has received at least `(k + 1) * C i` slots. The bound is `2 * ((2:ℝ) ^ ((1:ℝ)/2) - 1)`.
--
--   **Why this is a variation.** A variation on the open platform problem LiuLayland1973.rate_monotonic_utilization_bound (every job meets its deadline when the utilization is at most n(2^{1/n} - 1)), played at n = 2 with the parent's schedule model and conclusion restated verbatim, not imported. n = 1 is the condition utilization <= 1, so n = 2 is the first non-trivial size. The statement for all n remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   C. L. Liu and J. W. Layland, Scheduling algorithms for multiprogramming in a hard-real-time environment, Journal of the ACM 20(1) (1973), 46-61; the bound n(2^{1/n} - 1) is their Theorem 5 (theorem number and pages cited from memory). The statement was also checked by exhaustive simulation over one hyperperiod for all integer periods T_0, T_1 <= 30 and all run times C_i <= T_i with utilization <= 2(sqrt 2 - 1) (63066 instances, no missed deadline).

import Mathlib

namespace LefebvreVariations

/-- Rate-monotonic scheduling with two tasks, in the discrete-time model of the Liu–Layland
platform problem: tasks `Fin 2`, task `i` runs `C i` unit slots every `T i`, releasing its `k`-th
job at `k * T i` with deadline `(k + 1) * T i`; `σ t` is the highest-priority (shortest period,
ties by index) task with pending work, or idle. two tasks: if the utilization is at most `2 (√2 − 1) ≈ 0.828`, every job meets its deadline.
Source: C. L. Liu and J. W. Layland, *Scheduling algorithms for multiprogramming in a hard-real-time
environment*, J. ACM 20 (1973) (Theorem 5, the bound `n (2^{1/n} − 1)`; cited from memory). Checked by simulation over all periods up to 30. -/
theorem rate_monotonic_two_tasks (C T : Fin 2 → ℕ)
    (hC : ∀ i, 1 ≤ C i) (hCT : ∀ i, C i ≤ T i)
    (hU : ∑ i, (C i : ℝ) / (T i : ℝ) ≤ 2 * ((2 : ℝ) ^ ((1 : ℝ) / 2) - 1))
    (σ : ℕ → Option (Fin 2))
    (hσ : ∀ (t : ℕ) (i : Fin 2), σ t = some i ↔
      (((Finset.range t).filter (fun s => σ s = some i)).card <
          C i * ((Finset.range (t + 1)).filter (fun k => k * T i ≤ t)).card) ∧
      ∀ j : Fin 2, (T j < T i ∨ (T j = T i ∧ j < i)) →
        C j * ((Finset.range (t + 1)).filter (fun k => k * T j ≤ t)).card ≤
          ((Finset.range t).filter (fun s => σ s = some j)).card)
    (i : Fin 2) (k : ℕ) :
    (k + 1) * C i ≤
      ((Finset.range ((k + 1) * T i)).filter (fun s => σ s = some i)).card := by
  sorry

end LefebvreVariations
