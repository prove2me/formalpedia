-- Prove2me | Theorems.Thm_Newton_su2_adjointSq_13
-- name    : Newton.su2_adjointSq_13
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:57.412559+00:00
-- url     : https://prove2.me/theorems/d073d6ea-594a-5cf0-b11d-3ee1cde8f684
-- title:
--   Newton: su2 adjoint Sq 13
-- statement:
--   [T₁, [T₁, T₃]] = [T₁, -T₂] = T₃
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L452-L453
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L452-L453

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_adjointSq_13 : ⁅su2Gen1, ⁅su2Gen1, su2Gen3⁆⁆ = -su2Gen3 := by sorry
