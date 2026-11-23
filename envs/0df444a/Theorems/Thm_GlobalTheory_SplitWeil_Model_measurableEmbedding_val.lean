-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
-- name    : GlobalTheory.SplitWeil.Model.measurableEmbedding_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:25.673838+00:00
-- url     : https://prove2.me/theorems/fcb81915-18c2-44df-999c-e58a74ef7d9e
-- title:
--   Model: measurable Embedding val
-- statement:
--   The Model construction uses the measurable Embedding val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L172-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L172-L183

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

theorem GlobalTheory.SplitWeil.Model.measurableEmbedding_val (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (fun g : GL n k => g.val) := by sorry
