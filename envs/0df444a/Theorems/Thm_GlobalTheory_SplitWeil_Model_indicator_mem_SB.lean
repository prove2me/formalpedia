-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_Model_indicator_mem_SB
-- name    : GlobalTheory.SplitWeil.Model.indicator_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:24.719569+00:00
-- url     : https://prove2.me/theorems/758c91df-b60e-4d90-a9bd-16188923af5e
-- title:
--   Model: indicator mem SB
-- statement:
--   The Model construction uses the indicator mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L186-L190

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
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitWeil.Model.indicator_mem_SB : (𝒪[k] : Set k).indicator (fun _ => (1 : ℂ)) ∈ SB k := by sorry
