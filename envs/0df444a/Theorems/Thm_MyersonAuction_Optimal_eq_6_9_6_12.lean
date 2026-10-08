-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_eq_6_9_6_12
-- name    : MyersonAuction.Optimal.eq_6_9_6_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:31.505482+00:00
-- url     : https://prove2.me/theorems/655ec83b-0cf9-45f0-a0e4-2b5d7eb70a7d
-- title:
--   Equations (6.9), (6.12) — ironing does not increase virtual surplus for monotone allocations
-- statement:
--   For an allocation rule satisfying the single-object constraint and weak monotonicity of the interim win probability, the expected difference between the original quantile virtual value and the ironed slope, weighted by bidder $i$’s allocation probability, is nonpositive:
--
--   $$\int_T\bigl(h_i(F_i(t_i))-g_i(F_i(t_i))\bigr)p_i(t)f(t)\,dt\le0.$$
--
--   This is the combined implication of Myerson’s integration-by-parts identity (6.9) and the nonnegative Stieltjes integral (6.12).
--
--   **Formalization Note** The theorem states the ordinary-integral consequence instead of introducing a Lebesgue–Stieltjes measure for $dQ_i$.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), pp. 69–70, eqs. (6.9), (6.12)

import Definitions.Def_MyersonAuction_Optimal_Ironing

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

theorem eq_6_9_6_12 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p : Outcome ι)
    (hp : AdmissibleAllocation E p) (i : ι) :
    (∫ t, (h E i (F E i (t i)) - g E i (F E i (t i))) * p i t
      ∂distribution E) ≤ 0 := by sorry

end MyersonAuction.Optimal
