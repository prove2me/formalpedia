-- Prove2me | Theorems.Thm_Newton_adjointAction_compose
-- name    : Newton.adjointAction.compose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:51:51.767197+00:00
-- url     : https://prove2.me/theorems/75c01ffb-b99e-4040-8c6f-31f6df7f7ca1
-- title:
--   adjoint Action: compose
-- statement:
--   Composition rule for adjoint action: Ad(gh)(A) = Ad(g)(Ad(h)(A))
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L156-L161
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L156-L161

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

theorem Newton.adjointAction.compose (g h : SUNGroup N) (A : SuNAlgebra N) :
    adjointAction (g * h) A = adjointAction g (adjointAction h A) := by sorry
