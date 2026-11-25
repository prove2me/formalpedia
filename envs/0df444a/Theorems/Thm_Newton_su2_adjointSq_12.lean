-- Prove2me | Theorems.Thm_Newton_su2_adjointSq_12
-- name    : Newton.su2_adjointSq_12
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:25.5261+00:00
-- url     : https://prove2.me/theorems/3d3bfd14-490a-40f9-b4a9-dc061d7e43a9
-- title:
--   Newton: su2 adjoint Sq 12
-- statement:
--   [T₁, [T₁, T₂]] = [T₁, T₃] = -T₂
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L444-L445
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L444-L445

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_adjointSq_12 : ⁅su2Gen1, ⁅su2Gen1, su2Gen2⁆⁆ = -su2Gen2 := by sorry
