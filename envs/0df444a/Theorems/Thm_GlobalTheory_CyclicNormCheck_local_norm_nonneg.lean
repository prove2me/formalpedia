-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_local_norm_nonneg
-- name    : GlobalTheory.CyclicNormCheck.local_norm_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:29.282956+00:00
-- url     : https://prove2.me/theorems/6a801a82-0684-4ed5-b833-8f954c9b4264
-- title:
--   Cyclic Norm Check: local norm nonneg
-- statement:
--   The Cyclic Norm Check construction uses the local norm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L140-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L140-L172

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

theorem GlobalTheory.CyclicNormCheck.local_norm_nonneg {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ] [CharZero F]
    [Module.Finite F E] (hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ)
    (y : ℝ ⊗[F] E) : 0 ≤ Algebra.norm ℝ y := by sorry
