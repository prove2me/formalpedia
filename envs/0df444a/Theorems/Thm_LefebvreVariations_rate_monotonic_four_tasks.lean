-- Prove2me | Theorems.Thm_LefebvreVariations_rate_monotonic_four_tasks
-- name    : LefebvreVariations.rate_monotonic_four_tasks
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:36:40.308806+00:00
-- url     : https://prove2.me/theorems/794fb0a1-987b-5ff2-b238-fe9d9c11b99b
-- title:
--   Lefebvre's variations, No. 189 — on a theme by Liu and Layland: rate-monotonic scheduling of four tasks meets every deadline when the utilization is at most 4(2^{1/4} − 1)
-- statement:
--   Let $C_i,T_i$ ($i=0,1,2,3$) be positive integers with $C_i\le T_i$ and
--   $$
--   \sum_{i=0}^{3}\frac{C_i}{T_i}\ \le\ 4\left(2^{1/4}-1\right).
--   $$
--   Then in the rate-monotonic schedule of the four periodic tasks, every job meets its deadline:
--   $$
--   \#\{\,s<(k+1)T_i : \text{task } i \text{ runs in slot } s\,\}\ \ge\ (k+1)\,C_i\qquad\text{for all } i\in\{0,1,2,3\},\ k\ge 0 .
--   $$
--
--   This is the case $n=4$ of the Liu–Layland utilization bound $n\,(2^{1/n}-1)$, which the platform lists as open for every $n$.
--
--   Time is divided into unit slots. Task $i$ releases its $k$-th job at time $kT_i$, with deadline $(k+1)T_i$ and $C_i$ slots of work; in every slot the processor runs the pending task with the shortest period (ties broken by the smaller index), or idles if none is pending. This is the rate-monotonic schedule of Liu and Layland in discrete time.
--
--   **Formalization Note** The tasks are `Fin 4`, with `C T : Fin 4 → ℕ`, `1 ≤ C i ≤ T i`. The schedule `σ : ℕ → Option (Fin 4)` is characterised by the hypothesis `hσ`: `σ t = some i` iff task `i` has pending work at `t` (its service so far is below `C i` times the number of jobs released by `t`, which is `⌊t / T i⌋ + 1`) and no higher-priority task has pending work. This determines `σ` uniquely by recursion on `t`. The conclusion says that by time `(k + 1) * T i` task `i` has received at least `(k + 1) * C i` slots. The bound is `4 * ((2:ℝ) ^ ((1:ℝ)/4) - 1)`.
--
--   **Why this is a variation.** A variation on the open platform problem LiuLayland1973.rate_monotonic_utilization_bound (utilization at most n(2^{1/n} - 1) guarantees every deadline under rate-monotonic scheduling), played at n = 4 with the parent's schedule model and conclusion restated verbatim, not imported. The statement for all n remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   C. L. Liu and J. W. Layland, Scheduling algorithms for multiprogramming in a hard-real-time environment, Journal of the ACM 20(1) (1973), 46-61 (bibliographic data confirmed by search); the bound n(2^{1/n} - 1), sufficient for rate-monotonic schedulability, is their Theorem 5 (theorem number cited from memory). For n = 4 the bound is irrational, so 'at most' and 'less than' coincide for rational utilizations. Independent check by exact response-time analysis (cross-validated against slot-by-slot simulation for n = 2, 3): all 24461 integer instances with sorted periods T_i <= 14 and utilization <= 4(2^{1/4} - 1), plus about 550000 random and near-extremal instances with periods up to 200, no missed deadline; the same checker rejects 1326 of 4700 instances slightly above the bound.

import Mathlib

namespace LefebvreVariations

/-- Rate-monotonic scheduling with four tasks, in the discrete-time model of the Liu–Layland
platform problem: tasks `Fin 4`, task `i` runs `C i` unit slots every `T i`, releasing its `k`-th
job at `k * T i` with deadline `(k + 1) * T i`; `σ t` is the highest-priority (shortest period,
ties by index) task with pending work, or idle. Four tasks: if the utilization is at most `4 (2^{1/4} − 1) ≈ 0.757`, every job meets its deadline.
Source: C. L. Liu and J. W. Layland, *Scheduling algorithms for multiprogramming in a hard-real-time
environment*, J. ACM 20 (1973) (Theorem 5, the bound `n (2^{1/n} − 1)`; cited from memory). Checked by simulation for all sorted periods up to 8 (118 instances only, since four tasks rarely fit under the bound with small periods). -/
theorem rate_monotonic_four_tasks (C T : Fin 4 → ℕ)
    (hC : ∀ i, 1 ≤ C i) (hCT : ∀ i, C i ≤ T i)
    (hU : ∑ i, (C i : ℝ) / (T i : ℝ) ≤ 4 * ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1))
    (σ : ℕ → Option (Fin 4))
    (hσ : ∀ (t : ℕ) (i : Fin 4), σ t = some i ↔
      (((Finset.range t).filter (fun s => σ s = some i)).card <
          C i * ((Finset.range (t + 1)).filter (fun k => k * T i ≤ t)).card) ∧
      ∀ j : Fin 4, (T j < T i ∨ (T j = T i ∧ j < i)) →
        C j * ((Finset.range (t + 1)).filter (fun k => k * T j ≤ t)).card ≤
          ((Finset.range t).filter (fun s => σ s = some j)).card)
    (i : Fin 4) (k : ℕ) :
    (k + 1) * C i ≤
      ((Finset.range ((k + 1) * T i)).filter (fun s => σ s = some i)).card := by
  sorry

end LefebvreVariations
