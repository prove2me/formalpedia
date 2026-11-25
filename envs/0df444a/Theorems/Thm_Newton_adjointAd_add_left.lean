-- Prove2me | Theorems.Thm_Newton_adjointAd_add_left
-- name    : Newton.adjointAd_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:22.562917+00:00
-- url     : https://prove2.me/theorems/f8654fab-1d3d-4d9b-a275-e520d0153960
-- title:
--   Newton: adjoint Ad add left
-- statement:
--   Left linearity of ad action: ad(A + B) = ad(A) + ad(B)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L81-L84
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L81-L84

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.adjointAd_add_left (A B C : SuNAlgebra N) :
    adjointAd (A + B) C = adjointAd A C + adjointAd B C := by sorry
