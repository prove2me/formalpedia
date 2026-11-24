-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_Model_IsUnram_isTame
-- name    : GlobalTheory.SplitWeil.Model.IsUnram.isTame
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:37.131892+00:00
-- url     : https://prove2.me/theorems/f6c5be91-e77c-4eb8-97e6-ec1e30bc7762
-- title:
--   Is Unram: is Tame
-- statement:
--   The Is Unram construction uses the is Tame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L129-L130

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

theorem GlobalTheory.SplitWeil.Model.IsUnram.isTame {μ : kˣ →* ℂˣ} (h : IsUnram μ) : IsTame μ := by sorry
