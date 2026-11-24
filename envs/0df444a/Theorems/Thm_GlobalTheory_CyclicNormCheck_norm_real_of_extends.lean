-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_real_of_extends
-- name    : GlobalTheory.CyclicNormCheck.norm_real_of_extends
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:16.21363+00:00
-- url     : https://prove2.me/theorems/d92a0407-167f-4e73-b639-9c6b41b6388e
-- title:
--   Cyclic Norm Check: norm real of extends
-- statement:
--   The Cyclic Norm Check construction uses the norm real of extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L129-L138

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

theorem GlobalTheory.CyclicNormCheck.norm_real_of_extends {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ]
    [Module.Finite F E] [IsGalois F E] (τ : E →+* ℝ) (hτ : τ.comp (algebraMap F E) = algebraMap F ℝ)
    {a : ℝ} (ha : a ≠ 0) : ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = a := by sorry
