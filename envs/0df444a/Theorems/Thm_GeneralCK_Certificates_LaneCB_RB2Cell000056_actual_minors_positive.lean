-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell000056_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell000056.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T14:19:47.011993+00:00
-- url     : https://prove2.me/theorems/f54b61ce-b483-42cb-8cc8-4f7ebfb44c9a
-- title:
--   Correction matrix positivity on RB2 cell 000056
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

theorem GeneralCK.Certificates.LaneCB.RB2Cell000056.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (131/1280:ℝ) (263/2560))
    (hr : rho∈Icc (73/640:ℝ) (301/2560)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
