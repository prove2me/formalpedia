-- Prove2me | Theorems.Thm_GroundTheory_Global_variableChange_rst_eq_zero
-- name    : GroundTheory.Global.variableChange_rst_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:47.05018+00:00
-- url     : https://prove2.me/theorems/0a53bf2e-9332-4e43-94df-c38370b81b42
-- title:
--   Global: variable Change rst eq zero
-- statement:
--   The Global construction uses the variable Change rst eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L78-L89

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
variable [CharZero F]

theorem GroundTheory.Global.variableChange_rst_eq_zero {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by sorry
