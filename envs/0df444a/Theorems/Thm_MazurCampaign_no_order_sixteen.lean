-- Prove2me | Theorems.Thm_MazurCampaign_no_order_sixteen
-- name    : MazurCampaign.no_order_sixteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T09:00:18.825063+00:00
-- url     : https://prove2.me/theorems/89c2557f-52a3-4c92-a570-ef8322b91fc8
-- title:
--   No rational torsion of order 16
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $16$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 16.$$ Ellipticity is the only curve hypothesis. This is one of the nine unconditional composite-order exclusions established in the MazurTheorem WIP; its exact transfer contract remains open on this platform until a checked proof is accepted.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Kubert/OrderSixteenReduction.lean#L1082

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_sixteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 16 := by sorry
