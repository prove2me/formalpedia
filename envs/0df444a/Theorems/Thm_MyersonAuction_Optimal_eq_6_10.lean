-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_eq_6_10
-- name    : MyersonAuction.Optimal.eq_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:34.399082+00:00
-- url     : https://prove2.me/theorems/0695b1de-a097-48df-9e43-02673707dcd4
-- title:
--   Equation (6.10) — splitting virtual surplus into ironed surplus and a correction
-- statement:
--   For a measurable allocation rule satisfying the single-object constraint, expected virtual surplus splits into expected ironed surplus and the bidder-wise correction terms:
--
--   $$
--   \int_T\sum_i(c_i(t_i)-t_0)p_i(t)f(t)\,dt=
--   \int_T\sum_i(\bar c_i(t_i)-t_0)p_i(t)f(t)\,dt+
--   \sum_i\int_T(h_i(F_i(t_i))-g_i(F_i(t_i)))p_i(t)f(t)\,dt.
--   $$
--
--   This is the first-to-third-line equality in the paper’s equation (6.10); its final Stieltjes form follows from (6.9).
--
--   **Formalization Note** Each allocation component is required to be integrable under the profile law.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 69, eq. (6.10)

import Definitions.Def_MyersonAuction_Optimal_Ironing

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

theorem eq_6_10 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p : Outcome ι)
    (hp : ProbabilityCondition E p)
    (hmeas : ∀ i, Integrable (p i) (distribution E)) :
    virtualObjective E p =
      (∫ t, (∑ i, (ironedPriority E i (t i) - E.t0) * p i t)
        ∂distribution E) +
      ∑ i, (∫ t, (h E i (F E i (t i)) - g E i (F E i (t i))) * p i t
        ∂distribution E) := by sorry

end MyersonAuction.Optimal
