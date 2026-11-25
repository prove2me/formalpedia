-- Prove2me | Theorems.Thm_Newton_su2_bracket_21
-- name    : Newton.su2_bracket_21
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:28.527205+00:00
-- url     : https://prove2.me/theorems/750a713d-0652-41a0-9c4b-62560e3eb03a
-- title:
--   Newton: su2 bracket 21
-- statement:
--   [T₂, T₁] = -T₃ (by antisymmetry)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L409-L410
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L409-L410

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_bracket_21 : ⁅su2Gen2, su2Gen1⁆ = -su2Gen3 := by sorry
