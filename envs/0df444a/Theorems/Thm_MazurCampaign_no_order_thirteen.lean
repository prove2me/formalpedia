-- Prove2me | Theorems.Thm_MazurCampaign_no_order_thirteen
-- name    : MazurCampaign.no_order_thirteen
-- status  : Open
-- author  : @Vas
-- created : 2026-10-06T08:33:20.506754+00:00
-- url     : https://prove2.me/theorems/0cef6cc2-37da-4490-9b55-284e4f5b67b5
-- title:
--   No rational torsion of order thirteen
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $13$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 13.$$ Ellipticity is the only curve hypothesis. This is an explicit remaining exclusion used by the full point-order classification in the Mazur mission.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/PointOrder.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_thirteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 13 := by sorry
