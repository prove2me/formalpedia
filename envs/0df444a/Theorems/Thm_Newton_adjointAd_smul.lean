-- Prove2me | Theorems.Thm_Newton_adjointAd_smul
-- name    : Newton.adjointAd.smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:02:20.251794+00:00
-- url     : https://prove2.me/theorems/9f451a10-181c-448c-82e3-18a15b3dd7cf
-- title:
--   adjoint Ad: smul
-- statement:
--   ad action preserves scalar multiplication: ad(A)(r • B) = r • ad(A)(B)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L26-L31
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L26-L31

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd

theorem Newton.adjointAd.smul (A : SuNAlgebra N) (r : ℝ) (B : SuNAlgebra N) :
    adjointAd A (r • B) = r • adjointAd A B := by sorry
