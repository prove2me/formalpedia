-- Prove2me | Theorems.Thm_MazurCampaign_no_order_fourteen
-- name    : MazurCampaign.no_order_fourteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T09:26:51.819812+00:00
-- url     : https://prove2.me/theorems/5f8210fe-6eb6-4515-89dc-94ae76566268
-- title:
--   No rational torsion of order 14
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $14$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 14.$$ Ellipticity is the only curve hypothesis. This is one of the nine unconditional composite-order exclusions established in the MazurTheorem WIP; its exact transfer contract remains open on this platform until a checked proof is accepted.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Kubert/OrderFourteen.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_fourteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 14 := by sorry
