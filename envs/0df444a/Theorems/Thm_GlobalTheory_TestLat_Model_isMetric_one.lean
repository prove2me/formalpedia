-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_isMetric_one
-- name    : GlobalTheory.TestLat.Model.isMetric_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:48.36924+00:00
-- url     : https://prove2.me/theorems/c85ca46c-7144-5e06-bd42-08488749f77a
-- title:
--   Model: is Metric one
-- statement:
--   The Model construction uses the is Metric one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L72-L74

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

theorem GlobalTheory.TestLat.Model.isMetric_one : IsMetric (1 : Matrix (Fin N) (Fin N) K) fun _ => 1 := by sorry
