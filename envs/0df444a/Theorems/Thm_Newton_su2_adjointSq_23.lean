-- Prove2me | Theorems.Thm_Newton_su2_adjointSq_23
-- name    : Newton.su2_adjointSq_23
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:58:06.073119+00:00
-- url     : https://prove2.me/theorems/d883846d-fcc9-4db0-a711-81e638063f20
-- title:
--   Newton: su2 adjoint Sq 23
-- statement:
--   [T₂, [T₂, T₃]] = [T₂, T₁] = -T₃
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L456-L457
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L456-L457

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_adjointSq_23 : ⁅su2Gen2, ⁅su2Gen2, su2Gen3⁆⁆ = -su2Gen3 := by sorry
