-- Prove2me | Theorems.Thm_Newton_adjointAd2_def
-- name    : Newton.adjointAd2_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:49.395364+00:00
-- url     : https://prove2.me/theorems/9e58d50d-3d3b-4230-95d5-42f35cb5f713
-- title:
--   Newton: adjoint Ad2 def
-- statement:
--   Expansion of ad(A)^2(B) = [A, [A, B]]
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L106-L107
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L106-L107

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.adjointAd2_def (A B : SuNAlgebra N) :
    adjointAd2 A B = ⁅A, ⁅A, B⁆⁆ := by sorry
