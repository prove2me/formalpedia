-- Prove2me | Theorems.Thm_GroundTheory_Global_variableChangePoint_some
-- name    : GroundTheory.Global.variableChangePoint_some
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:45.692837+00:00
-- url     : https://prove2.me/theorems/e03fda70-f29d-4915-9d37-07e935063f66
-- title:
--   Global: variable Change Point some
-- statement:
--   The Global construction uses the variable Change Point some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/VariableChangePoints.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/VariableChangePoints.lean#L48-L52

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open WeierstrassCurve
variable {F : Type*} [Field F]

theorem GroundTheory.Global.variableChangePoint_some (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint C hC (.some x y h) =
      .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        (by subst hC; exact nonsingular_variableChange C W h) := by sorry
