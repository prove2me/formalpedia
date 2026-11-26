-- Prove2me | Theorems.Thm_LefebvreVariations_rate_monotonic_three_tasks
-- name    : LefebvreVariations.rate_monotonic_three_tasks
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:36:24.678468+00:00
-- url     : https://prove2.me/theorems/a9895642-88f4-4de3-9a5e-53f0b267b4f0
-- title:
--   Lefebvre's variations, No. 226 — on a theme by Liu and Layland: rate-monotonic scheduling of three tasks meets every deadline when the utilization is at most 3(2^{1/3} − 1)
-- statement:
--   Let $C_i,T_i$ ($i=0,1,2$) be positive integers with $C_i\le T_i$ and
--   $$
--   \sum_{i=0}^{2}\frac{C_i}{T_i}\ \le\ 3\left(2^{1/3}-1\right).
--   $$
--   Then in the rate-monotonic schedule of the three periodic tasks, every job meets its deadline:
--   $$
--   \#\{\,s<(k+1)T_i : \text{task } i \text{ runs in slot } s\,\}\ \ge\ (k+1)\,C_i\qquad\text{for all } i\in\{0,1,2\},\ k\ge 0 .
--   $$
--
--   This is the case $n=3$ of the Liu–Layland utilization bound $n\,(2^{1/n}-1)$, which the platform lists as open for every $n$.
--
--   Time is divided into unit slots. Task $i$ releases its $k$-th job at time $kT_i$, with deadline $(k+1)T_i$ and $C_i$ slots of work; in every slot the processor runs the pending task with the shortest period (ties broken by the smaller index), or idles if none is pending. This is the rate-monotonic schedule of Liu and Layland in discrete time.
--
--   **Formalization Note** The tasks are `Fin 3`, with `C T : Fin 3 → ℕ`, `1 ≤ C i ≤ T i`. The schedule `σ : ℕ → Option (Fin 3)` is characterised by the hypothesis `hσ`: `σ t = some i` iff task `i` has pending work at `t` (its service so far is below `C i` times the number of jobs released by `t`, which is `⌊t / T i⌋ + 1`) and no higher-priority task has pending work. This determines `σ` uniquely by recursion on `t`. The conclusion says that by time `(k + 1) * T i` task `i` has received at least `(k + 1) * C i` slots. The bound is `3 * ((2:ℝ) ^ ((1:ℝ)/3) - 1)`.
--
--   **Why this is a variation.** A variation on the open platform problem LiuLayland1973.rate_monotonic_utilization_bound (utilization at most n(2^{1/n} - 1) guarantees every deadline under rate-monotonic scheduling), played at n = 3 with the parent's schedule model and conclusion restated verbatim, not imported. The statement for all n remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   C. L. Liu and J. W. Layland, Scheduling algorithms for multiprogramming in a hard-real-time environment, Journal of the ACM 20(1) (1973), 46-61; the bound n(2^{1/n} - 1) is their Theorem 5 (theorem number and pages cited from memory). The statement was also checked by exhaustive simulation over one hyperperiod for all integer periods T_i <= 10 and all run times C_i <= T_i with utilization <= 3(2^{1/3} - 1) (3805 instances, no missed deadline).

import Mathlib

namespace LefebvreVariations

/-- Rate-monotonic scheduling with three tasks, in the discrete-time model of the Liu–Layland
platform problem: tasks `Fin 3`, task `i` runs `C i` unit slots every `T i`, releasing its `k`-th
job at `k * T i` with deadline `(k + 1) * T i`; `σ t` is the highest-priority (shortest period,
ties by index) task with pending work, or idle. three tasks: if the utilization is at most `3 (2^{1/3} − 1) ≈ 0.780`, every job meets its deadline.
Source: C. L. Liu and J. W. Layland, *Scheduling algorithms for multiprogramming in a hard-real-time
environment*, J. ACM 20 (1973) (Theorem 5, the bound `n (2^{1/n} − 1)`; cited from memory). Checked by simulation over all periods up to 10. -/
theorem rate_monotonic_three_tasks (C T : Fin 3 → ℕ)
    (hC : ∀ i, 1 ≤ C i) (hCT : ∀ i, C i ≤ T i)
    (hU : ∑ i, (C i : ℝ) / (T i : ℝ) ≤ 3 * ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1))
    (σ : ℕ → Option (Fin 3))
    (hσ : ∀ (t : ℕ) (i : Fin 3), σ t = some i ↔
      (((Finset.range t).filter (fun s => σ s = some i)).card <
          C i * ((Finset.range (t + 1)).filter (fun k => k * T i ≤ t)).card) ∧
      ∀ j : Fin 3, (T j < T i ∨ (T j = T i ∧ j < i)) →
        C j * ((Finset.range (t + 1)).filter (fun k => k * T j ≤ t)).card ≤
          ((Finset.range t).filter (fun s => σ s = some j)).card)
    (i : Fin 3) (k : ℕ) :
    (k + 1) * C i ≤
      ((Finset.range ((k + 1) * T i)).filter (fun s => σ s = some i)).card := by
  sorry

end LefebvreVariations
