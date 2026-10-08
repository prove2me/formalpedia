-- Prove2me | Theorems.Thm_MazurCampaign_no_order_thirty_five
-- name    : MazurCampaign.no_order_thirty_five
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T08:33:33.371847+00:00
-- url     : https://prove2.me/theorems/ba7a85bd-12d8-4826-8c04-502e89accda4
-- title:
--   No rational torsion of order thirty-five
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $35$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 35.$$ Ellipticity is the only curve hypothesis. This is an explicit remaining exclusion used by the full point-order classification in the Mazur mission.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/PointOrder.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_thirty_five
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 35 := by sorry
