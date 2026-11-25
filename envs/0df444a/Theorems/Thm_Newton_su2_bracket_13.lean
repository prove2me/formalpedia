-- Prove2me | Theorems.Thm_Newton_su2_bracket_13
-- name    : Newton.su2_bracket_13
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:42.95845+00:00
-- url     : https://prove2.me/theorems/d1dbacbc-7dde-49ce-9bb6-c02ff0ce54f9
-- title:
--   Newton: su2 bracket 13
-- statement:
--   [T₁, T₃] = -T₂ (by antisymmetry)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L417-L418
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L417-L418

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_bracket_13 : ⁅su2Gen1, su2Gen3⁆ = -su2Gen2 := by sorry
