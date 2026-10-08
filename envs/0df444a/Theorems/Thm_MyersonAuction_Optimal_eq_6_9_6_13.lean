-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_eq_6_9_6_13
-- name    : MyersonAuction.Optimal.eq_6_9_6_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:44.59989+00:00
-- url     : https://prove2.me/theorems/a559825b-c637-424d-8291-b4a9a18246f3
-- title:
--   Equations (6.9), (6.13) — the ironing correction vanishes for the proposed allocation
-- statement:
--   For Myerson’s proposed allocation $\bar p$, the correction between original and ironed virtual values vanishes for every bidder:
--
--   $$\int_T\bigl(h_i(F_i(t_i))-g_i(F_i(t_i))\bigr)\bar p_i(t)f(t)\,dt=0.$$
--
--   This is the ordinary-integral form obtained by combining the integration-by-parts identity (6.9) with the vanishing Stieltjes integral (6.13).
--
--   **Formalization Note** The integral over supported profiles uses the normalized product law.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), pp. 69–70, eqs. (6.9), (6.13)

import Definitions.Def_MyersonAuction_Optimal_Ironing

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

theorem eq_6_9_6_13 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (i : ι) :
    (∫ t, (h E i (F E i (t i)) - g E i (F E i (t i))) * pbar E i t
      ∂distribution E) = 0 := by sorry

end MyersonAuction.Optimal
