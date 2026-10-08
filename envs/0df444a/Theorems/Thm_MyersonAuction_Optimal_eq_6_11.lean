-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_eq_6_11
-- name    : MyersonAuction.Optimal.eq_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:38.665507+00:00
-- url     : https://prove2.me/theorems/9fd492de-36b9-4eae-a65d-4fd78e2b3bd9
-- title:
--   Equation (6.11) — the proposed allocation maximizes ironed surplus
-- statement:
--   Myerson’s proposed allocation $\bar p$ satisfies the single-object probability constraint and attains at least as much expected ironed surplus as any other admissible allocation $p$:
--
--   $$
--   \int_T\sum_i(\bar c_i(t_i)-t_0)p_i(t)f(t)\,dt
--   \le\int_T\sum_i(\bar c_i(t_i)-t_0)\bar p_i(t)f(t)\,dt.
--   $$
--
--   The result is the pointwise maximization step in the proof of the main theorem.
--
--   **Formalization Note** The competing allocation components are integrable.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 69, eq. (6.11) and following sentence

import Definitions.Def_MyersonAuction_Optimal_Ironing

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

theorem eq_6_11 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p : Outcome ι)
    (hp : ProbabilityCondition E p)
    (hmeas : ∀ i, Integrable (p i) (distribution E)) :
    ProbabilityCondition E (pbar E) ∧
      (∫ t, (∑ i, (ironedPriority E i (t i) - E.t0) * p i t)
        ∂distribution E) ≤
      (∫ t, (∑ i, (ironedPriority E i (t i) - E.t0) * pbar E i t)
        ∂distribution E) := by sorry

end MyersonAuction.Optimal
