-- Prove2me | Theorems.Thm_MazurCampaign_no_order_twenty_seven
-- name    : MazurCampaign.no_order_twenty_seven
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T09:27:39.659997+00:00
-- url     : https://prove2.me/theorems/683787ad-e0d2-4898-80ba-8f73f635c50b
-- title:
--   No rational torsion of order 27
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $27$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 27.$$ Ellipticity is the only curve hypothesis. This is one of the nine unconditional composite-order exclusions established in the MazurTheorem WIP; its exact transfer contract remains open on this platform until a checked proof is accepted.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Kubert/OrderTwentySeven.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_twenty_seven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 27 := by sorry
