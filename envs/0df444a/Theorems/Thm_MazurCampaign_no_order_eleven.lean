-- Prove2me | Theorems.Thm_MazurCampaign_no_order_eleven
-- name    : MazurCampaign.no_order_eleven
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T08:33:05.691782+00:00
-- url     : https://prove2.me/theorems/7bbee754-1c67-4b24-a23e-9f7a3d2d57ed
-- title:
--   No rational torsion of order eleven
-- statement:
--   For every elliptic curve $E/\mathbb Q$, no rational torsion point has exact order $11$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne 11.$$ Ellipticity is the only curve hypothesis. This is an explicit remaining exclusion used by the full point-order classification in the Mazur mission.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/PointOrder.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_eleven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 11 := by sorry
