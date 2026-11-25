-- Prove2me | Theorems.Thm_Newton_adjointAd_zero
-- name    : Newton.adjointAd.zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:29.117074+00:00
-- url     : https://prove2.me/theorems/f3d4f4ed-4987-4417-bb6d-6214c922faa4
-- title:
--   adjoint Ad: zero
-- statement:
--   ad action preserves zero: ad(A)(0) = 0
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L35-L37
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L35-L37

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd

theorem Newton.adjointAd.zero (A : SuNAlgebra N) : adjointAd A (0 : SuNAlgebra N) = 0 := by sorry
