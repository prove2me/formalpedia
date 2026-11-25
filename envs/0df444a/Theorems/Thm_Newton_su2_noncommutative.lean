-- Prove2me | Theorems.Thm_Newton_su2_noncommutative
-- name    : Newton.su2_noncommutative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:47:12.825846+00:00
-- url     : https://prove2.me/theorems/5cffbaf2-c6ed-4f13-b482-5523e7ddf297
-- title:
--   Newton: su2 noncommutative
-- statement:
--   Non-commutativity of su(2): [T₁, T₂] ≠ 0
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L404-L406
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L404-L406

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_noncommutative : ⁅su2Gen1, su2Gen2⁆ ≠ 0 := by sorry
