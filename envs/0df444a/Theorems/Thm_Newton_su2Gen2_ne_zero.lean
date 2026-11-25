-- Prove2me | Theorems.Thm_Newton_su2Gen2_ne_zero
-- name    : Newton.su2Gen2_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:53:12.268806+00:00
-- url     : https://prove2.me/theorems/2461a1cc-4d41-4fec-9272-bf982c6cfd3d
-- title:
--   Newton: su2 Gen2 ne zero
-- statement:
--   su2Gen2 is nonzero
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L428-L433
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L428-L433

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2Gen2_ne_zero : su2Gen2 ≠ 0 := by sorry
