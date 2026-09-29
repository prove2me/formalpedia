-- Prove2me | Theorems.Thm_GeneralCK_Correction_Mdet_pos_iff_Kfactored_pos
-- name    : GeneralCK.Correction.Mdet_pos_iff_Kfactored_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:51:56.895055+00:00
-- url     : https://prove2.me/theorems/226835c5-30c2-4dd9-9d51-a007ede01e14
-- title:
--   Positivity of the correction determinant in factored form
-- statement:
--   For real entropy coordinates $e,f$ with $0<f<1$, the correction determinant $M_{\rm det}(e,f)$ is positive if and only if the factored kernel $K_{\rm factored}(e,f)$ is positive.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessianFactored.lean#L58-L61

import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_correction_minors

open GeneralCK GeneralCK.Correction

theorem GeneralCK.Correction.Mdet_pos_iff_Kfactored_pos {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < Mdet e f ↔ 0 < Kfactored e f := by sorry
