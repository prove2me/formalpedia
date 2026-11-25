-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_neg_one_not_norm
-- name    : GlobalTheory.CyclicNormCheck.neg_one_not_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:23.750802+00:00
-- url     : https://prove2.me/theorems/dab1b73b-da03-5fee-9f99-3f73a6ef5ea9
-- title:
--   Cyclic Norm Check: neg one not norm
-- statement:
--   The Cyclic Norm Check construction uses the neg one not norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L188-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L188-L207

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck

theorem GlobalTheory.CyclicNormCheck.neg_one_not_norm (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {4} ℚ E] :
    IsGalois ℚ E ∧ IsCyclic (E ≃ₐ[ℚ] E) ∧ Module.finrank ℚ E = 2 ∧ ¬ ∃ y : E, Algebra.norm ℚ y = -1 := by sorry
