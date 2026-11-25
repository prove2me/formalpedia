-- Prove2me | Theorems.Thm_Newton_adjointAction_one_action
-- name    : Newton.adjointAction.one_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:42:56.222085+00:00
-- url     : https://prove2.me/theorems/47c21edc-c74c-4d1d-80c2-95b8836cd8ae
-- title:
--   adjoint Action: one action
-- statement:
--   Adjoint action by identity is the identity map
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L151-L153
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L151-L153

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

theorem Newton.adjointAction.one_action (A : SuNAlgebra N) : adjointAction (1 : SUNGroup N) A = A := by sorry
