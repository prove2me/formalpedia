-- Prove2me | Theorems.Thm_GeneralCK_Certificates_LaneCB_RB2Cell000060_actual_minors_positive
-- name    : GeneralCK.Certificates.LaneCB.RB2Cell000060.actual_minors_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T17:02:26.758705+00:00
-- url     : https://prove2.me/theorems/8cb0c11d-2e09-4011-8af9-81dd7c6087c3
-- title:
--   Correction matrix positivity on RB2 cell 000060
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

theorem GeneralCK.Certificates.LaneCB.RB2Cell000060.actual_minors_positive {u rho : ℝ} (hu : u∈Icc (131/1280:ℝ) (263/2560))
    (hr : rho∈Icc (31/256:ℝ) (319/2560)) (hr1 : rho < 1) :
    0 < _root_.GeneralCK.Correction.Mleft (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) ∧
    0 < _root_.GeneralCK.Correction.Mdet (_root_.GeneralCK.H u) (_root_.GeneralCK.H (u+rho*(1/2-u))) := by sorry
