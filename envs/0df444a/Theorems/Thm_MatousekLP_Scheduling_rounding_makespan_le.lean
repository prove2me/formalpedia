-- Prove2me | Theorems.Thm_MatousekLP_Scheduling_rounding_makespan_le
-- name    : MatousekLP.Scheduling.rounding_makespan_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:39:33.857436+00:00
-- url     : https://prove2.me/theorems/a91e85fd-94bc-4427-83ad-d28ee8fd9c5e
-- title:
--   Lemma 8.3.3 — rounding a basic optimal solution of LPR(T) gives makespan at most t* + T
-- statement:
--   Let $d_{ij} > 0$ be running times of $n$ jobs on $m$ machines and let $T \ge 0$. Suppose $(t^*, x^*)$ is an optimal solution of the linear program $\mathrm{LPR}(T)$ (so $\mathrm{LPR}(T)$ is feasible and $t^*$ is its optimal value) that satisfies Assumption 8.3.1. Then there is a schedule $\sigma$, assigning every job $j$ to a machine $\sigma(j)$ with
--   $$
--   x^*_{\sigma(j)\,j} > 0 \quad\text{for every job } j,
--   $$
--   whose makespan satisfies
--   $$
--   \max_{i} \sum_{j:\ \sigma(j) = i} d_{ij} \;\le\; t^* + T .
--   $$
--
--   The schedule rounds the fractional assignment $x^*$ along the edges of its support graph; this is the rounding step of the Lenstra–Shmoys–Tardos 2-approximation for scheduling on unrelated machines.
--
--   **Formalization Note** The book says "we can efficiently construct a schedule"; the running time of the construction is not formalized. What is formalized is the property of the schedule that the proof constructs: each job goes to a machine $i$ with $x^*_{ij} > 0$, i.e. along an edge of the support graph. Without this constraint the statement would still be meaningful but would not describe the rounding. Machines are `Fin m`, jobs `Fin n`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 152, Lemma 8.3.3 (proof pp. 152–153)

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation

namespace MatousekLP.Scheduling

/-- Lemma 8.3.3 (Matoušek–Gärtner, p. 152), in the form produced by its proof. Let
`T ≥ 0` and let `(t*, x*)` be an optimal solution of `LPR(T)` (so `LPR(T)` is feasible
and `t*` is its optimal value) satisfying Assumption 8.3.1. Then there is a schedule
`σ` that assigns every job `j` to a machine `σ(j)` with `x*_{σ(j) j} > 0` (along an
edge of the support graph `G`), and whose makespan is at most `t* + T`. -/
theorem rounding_makespan_le {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (T : ℝ) (hT : 0 ≤ T) (tstar : ℝ)
    (xstar : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d T tstar xstar) (hA : Assumption831 d T xstar) :
    ∃ σ : Fin n → Fin m, (∀ j, 0 < xstar (σ j) j) ∧ makespan d σ ≤ tstar + T := by sorry

end MatousekLP.Scheduling
