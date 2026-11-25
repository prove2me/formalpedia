-- Prove2me | Theorems.Thm_Newton_adjointAction_zero
-- name    : Newton.adjointAction.zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:18:17.366377+00:00
-- url     : https://prove2.me/theorems/310564aa-ca97-4cd8-8636-d90f9345d9c1
-- title:
--   adjoint Action: zero
-- statement:
--   Adjoint action preserves zero
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L172-L174
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L172-L174

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GaugeTransformation
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAction

theorem Newton.adjointAction.zero (g : SUNGroup N) : adjointAction g (0 : SuNAlgebra N) = 0 := by sorry
