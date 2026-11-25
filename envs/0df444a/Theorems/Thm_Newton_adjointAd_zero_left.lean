-- Prove2me | Theorems.Thm_Newton_adjointAd_zero_left
-- name    : Newton.adjointAd.zero_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:36.671999+00:00
-- url     : https://prove2.me/theorems/76297ccc-de1f-49a6-883c-f4c4aaad6848
-- title:
--   adjoint Ad: zero left
-- statement:
--   ad action of zero is the zero map: ad(0)(B) = 0
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L41-L43
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L41-L43

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd

theorem Newton.adjointAd.zero_left (B : SuNAlgebra N) : adjointAd (0 : SuNAlgebra N) B = 0 := by sorry
