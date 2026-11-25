-- Prove2me | Theorems.Thm_Newton_adjointAction_add
-- name    : Newton.adjointAction.add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:51:48.815215+00:00
-- url     : https://prove2.me/theorems/6ed1a02b-7ab1-5f78-856c-7978465d1019
-- title:
--   adjoint Action: add
-- statement:
--   Adjoint action preserves addition
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L164-L168
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L164-L168

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

theorem Newton.adjointAction.add (g : SUNGroup N) (A B : SuNAlgebra N) :
    adjointAction g (A + B) = adjointAction g A + adjointAction g B := by sorry
