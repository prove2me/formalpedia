-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_not_isMetric_zero
-- name    : GlobalTheory.TestLat.Model.not_isMetric_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:30.032457+00:00
-- url     : https://prove2.me/theorems/f5511b32-9f38-50f3-ac95-bd7a4c7c4f24
-- title:
--   Model: not is Metric zero
-- statement:
--   The Model construction uses the not is Metric zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L89-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

theorem GlobalTheory.TestLat.Model.not_isMetric_zero (X : InfinitePlace K → Matrix (Fin 1) (Fin 1) ℂ) : ¬ IsMetric (0 : Matrix (Fin 1) (Fin 1) K) X := by sorry
