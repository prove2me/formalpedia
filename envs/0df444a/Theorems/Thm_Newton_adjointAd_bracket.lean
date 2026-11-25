-- Prove2me | Theorems.Thm_Newton_adjointAd_bracket
-- name    : Newton.adjointAd_bracket
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:04:52.216733+00:00
-- url     : https://prove2.me/theorems/05f14bea-cf64-4f76-8500-8e7564f335ec
-- title:
--   Newton: adjoint Ad bracket
-- statement:
--   Composition rule for ad action
--
--   [[A, B], C] = [A, [B, C]] - [B, [A, C]]
--
--   This is a fundamental property of the adjoint representation of Lie algebras.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L75-L78
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L75-L78

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.adjointAd_bracket (A B C : SuNAlgebra N) :
    adjointAd ⁅A, B⁆ C = adjointAd A (adjointAd B C) - adjointAd B (adjointAd A C) := by sorry
