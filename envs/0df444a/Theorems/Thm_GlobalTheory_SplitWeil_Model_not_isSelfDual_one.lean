-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_Model_not_isSelfDual_one
-- name    : GlobalTheory.SplitWeil.Model.not_isSelfDual_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:17.774801+00:00
-- url     : https://prove2.me/theorems/1a57977b-c7ea-4a63-aae4-b66933e85438
-- title:
--   Model: not is Self Dual one
-- statement:
--   The Model construction uses the not is Self Dual one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L203-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L203-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitWeil.Model.not_isSelfDual_one (ν : Measure k) : ¬ IsSelfDual (1 : AddChar k Circle) ν := by sorry
