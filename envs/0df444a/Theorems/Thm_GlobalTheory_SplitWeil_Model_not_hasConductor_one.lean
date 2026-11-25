-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_Model_not_hasConductor_one
-- name    : GlobalTheory.SplitWeil.Model.not_hasConductor_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:26.817285+00:00
-- url     : https://prove2.me/theorems/45b4f4fc-d778-4b72-bce0-4bdd795237de
-- title:
--   Model: not has Conductor one
-- statement:
--   The Model construction uses the not has Conductor one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SecondCountableAndT2LocalField.lean#L76-L86

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

theorem GlobalTheory.SplitWeil.Model.not_hasConductor_one (c : kˣ) : ¬ HasConductor (1 : AddChar k Circle) c := by sorry
