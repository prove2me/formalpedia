-- Prove2me | Theorems.Thm_Newton_adjointAd_smul_left
-- name    : Newton.adjointAd_smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:49.489105+00:00
-- url     : https://prove2.me/theorems/f341d4fd-c5f3-4bed-9700-e4d7a492b84e
-- title:
--   Newton: adjoint Ad smul left
-- statement:
--   Left scalar multiplication of ad action: ad(r • A) = r • ad(A)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L87-L92
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L87-L92

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.adjointAd_smul_left (r : ℝ) (A B : SuNAlgebra N) :
    adjointAd (r • A) B = r • adjointAd A B := by sorry
