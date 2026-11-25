-- Prove2me | Theorems.Thm_Newton_adjointAction_bracket
-- name    : Newton.adjointAction.bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:52:01.777583+00:00
-- url     : https://prove2.me/theorems/799b6cf1-6b77-430c-b2f7-18294c1875e0
-- title:
--   adjoint Action: bracket
-- statement:
--   Adjoint action preserves Lie bracket
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L177-L201
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GaugeTransformation.lean#L177-L201

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

theorem Newton.adjointAction.bracket (g : SUNGroup N) (A B : SuNAlgebra N) :
    adjointAction g ⁅A, B⁆ = ⁅adjointAction g A, adjointAction g B⁆ := by sorry
