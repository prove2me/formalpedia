-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_eq_4_12
-- name    : MyersonAuction.Optimal.eq_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:46:37.603093+00:00
-- url     : https://prove2.me/theorems/4db284d7-9ad6-4ea0-8ca0-da071d4f155d
-- title:
--   Equation (4.12) — seller utility as virtual surplus
-- statement:
--   For every feasible direct mechanism, the seller’s expected utility equals virtual surplus plus the expected value of keeping the object, minus the bidders’ utilities at their lowest types:
--
--   $$
--   U_0(p,x)=\int_T\sum_i\left(c_i(t_i)-t_0\right)p_i(t)f(t)\,dt
--   +\int_Tv_0(t)f(t)\,dt-\sum_iU_i(p,x,a_i).
--   $$
--
--   The identity is the accounting step used to reduce optimal auction design to allocation choice.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 65, eq. (4.12)

import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

theorem eq_4_12 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p x : Outcome ι) (h : Feasible E p x) :
    sellerUtility E p x =
      virtualObjective E p +
      (∫ t, sellerValue E t ∂distribution E) -
      ∑ i, interimUtility E p x i (E.a i) := by sorry

end MyersonAuction.Optimal
