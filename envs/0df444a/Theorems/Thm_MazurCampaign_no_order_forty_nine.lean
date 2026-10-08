-- Prove2me | Theorems.Thm_MazurCampaign_no_order_forty_nine
-- name    : MazurCampaign.no_order_forty_nine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T09:27:45.597647+00:00
-- url     : https://prove2.me/theorems/6535522b-d119-4a64-a432-38f2456c6eb6
-- title:
--   No rational torsion of order 49
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $49$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 49.$$ Ellipticity is the only curve hypothesis. This is one of the nine unconditional composite-order exclusions established in the MazurTheorem WIP; its exact transfer contract remains open on this platform until a checked proof is accepted.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/NumberTheory/XZeroFortyNineTransfer.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_forty_nine
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 49 := by sorry
