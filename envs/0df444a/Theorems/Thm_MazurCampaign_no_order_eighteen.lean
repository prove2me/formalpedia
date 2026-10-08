-- Prove2me | Theorems.Thm_MazurCampaign_no_order_eighteen
-- name    : MazurCampaign.no_order_eighteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T09:27:15.240721+00:00
-- url     : https://prove2.me/theorems/f404bb2a-3c7e-4319-b7a1-29c8bf273c81
-- title:
--   No rational torsion of order 18
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $18$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 18.$$ Ellipticity is the only curve hypothesis. This is one of the nine unconditional composite-order exclusions established in the MazurTheorem WIP; its exact transfer contract remains open on this platform until a checked proof is accepted.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/PointOrder.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_eighteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 18 := by sorry
