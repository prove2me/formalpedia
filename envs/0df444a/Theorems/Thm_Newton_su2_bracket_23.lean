-- Prove2me | Theorems.Thm_Newton_su2_bracket_23
-- name    : Newton.su2_bracket_23
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:44:01.557971+00:00
-- url     : https://prove2.me/theorems/34d1d4b9-d78c-4000-9f4b-a1fb7f70fbf8
-- title:
--   Newton: su2 bracket 23
-- statement:
--   [T₂, T₃] = T₁
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L293-L308
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L293-L308

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_bracket_23 : ⁅su2Gen2, su2Gen3⁆ = su2Gen1 := by sorry
