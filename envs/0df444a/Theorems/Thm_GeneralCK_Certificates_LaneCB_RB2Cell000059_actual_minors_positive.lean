-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell000059_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell000059.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T17:02:08.233017+00:00
-- url     : https://prove2.me/theorems/106cf614-16df-4933-a8cc-0af698985348
-- title:
--   Correction matrix positivity on RB2 cell 000059
-- statement:
--   For real u and rho in the cell's specified closed intervals, with rho < 1, the correction matrix at (H(u), H(u + rho * (1/2 - u))) has strictly positive first diagonal entry and determinant. The exact endpoints appear in the formal statement.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_statement

open Set
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem GeneralCK.Certificates.LaneCB.RB2Cell000059.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (263/2560:ℝ) (33/320))
    (hr : rho∈Icc (301/2560:ℝ) (31/256)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
