-- Prove2me | Theorems.Thm_Newton_su2_adjointSq_21
-- name    : Newton.su2_adjointSq_21
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:15.360805+00:00
-- url     : https://prove2.me/theorems/28d039bd-c43e-4e17-86db-7efe6aef230a
-- title:
--   Newton: su2 adjoint Sq 21
-- statement:
--   [T₂, [T₂, T₁]] = [T₂, -T₃] = -[T₂, T₃] = -T₁
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L436-L437
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L436-L437

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_adjointSq_21 : ⁅su2Gen2, ⁅su2Gen2, su2Gen1⁆⁆ = -su2Gen1 := by sorry
