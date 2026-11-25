-- Prove2me | Theorems.Thm_Newton_su2_bracket_32
-- name    : Newton.su2_bracket_32
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:18.340496+00:00
-- url     : https://prove2.me/theorems/52ea26c9-62e8-46a1-9806-84c95ef2ba83
-- title:
--   Newton: su2 bracket 32
-- statement:
--   [T₃, T₂] = -T₁ (by antisymmetry)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L413-L414
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L413-L414

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_bracket_32 : ⁅su2Gen3, su2Gen2⁆ = -su2Gen1 := by sorry
