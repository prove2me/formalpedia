-- Prove2me | Theorems.Thm_Newton_su2Gen1_ne_zero
-- name    : Newton.su2Gen1_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:52:48.536586+00:00
-- url     : https://prove2.me/theorems/f89f66d6-63e7-4cab-9e88-d3e7214a40bf
-- title:
--   Newton: su2 Gen1 ne zero
-- statement:
--   su2Gen1 is nonzero
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L421-L425
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L421-L425

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2Gen1_ne_zero : su2Gen1 ≠ 0 := by sorry
