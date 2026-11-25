-- Prove2me | Theorems.Thm_Newton_su2_adjointSq_32
-- name    : Newton.su2_adjointSq_32
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:32.432672+00:00
-- url     : https://prove2.me/theorems/cbafc792-40bf-4b32-bb18-86c604a4f372
-- title:
--   Newton: su2 adjoint Sq 32
-- statement:
--   [T₃, [T₃, T₂]] = [T₃, T₁] = T₂
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L448-L449
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L448-L449

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_adjointSq_32 : ⁅su2Gen3, ⁅su2Gen3, su2Gen2⁆⁆ = -su2Gen2 := by sorry
