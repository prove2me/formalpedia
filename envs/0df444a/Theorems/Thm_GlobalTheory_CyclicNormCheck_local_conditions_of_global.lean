-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_local_conditions_of_global
-- name    : GlobalTheory.CyclicNormCheck.local_conditions_of_global
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:12.160811+00:00
-- url     : https://prove2.me/theorems/60910320-7506-579d-94f2-df493656adc9
-- title:
--   Cyclic Norm Check: local conditions of global
-- statement:
--   The Cyclic Norm Check construction uses the local conditions of global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L87-L95

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

theorem GlobalTheory.CyclicNormCheck.local_conditions_of_global (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) (hx : x ≠ 0) (h : ∃ y : E, Algebra.norm F y = x) :
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) ∧
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) := by sorry
