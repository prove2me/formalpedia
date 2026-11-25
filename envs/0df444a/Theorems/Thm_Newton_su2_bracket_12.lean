-- Prove2me | Theorems.Thm_Newton_su2_bracket_12
-- name    : Newton.su2_bracket_12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:42:49.098749+00:00
-- url     : https://prove2.me/theorems/1343d9a6-01c6-4a74-923c-a21df968bcc1
-- title:
--   Newton: su2 bracket 12
-- statement:
--   [T₁, T₂] = T₃
--
--   Calculation: [T₁, T₂] = [-iσ₁/2, -iσ₂/2] = (-i/2)² [σ₁, σ₂] = (-1/4)(2i σ₃) = (-i/2) σ₃ = T₃
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L213-L233
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L213-L233

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_bracket_12 : ⁅su2Gen1, su2Gen2⁆ = su2Gen3 := by sorry
