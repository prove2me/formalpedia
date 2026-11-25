-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_real_clause_iff
-- name    : GlobalTheory.CyclicNormCheck.real_clause_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:25.544402+00:00
-- url     : https://prove2.me/theorems/266cbe75-afb3-5350-81c0-aef890d46059
-- title:
--   Cyclic Norm Check: real clause iff
-- statement:
--   The Cyclic Norm Check construction uses the real clause iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L174-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L174-L186

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

theorem GlobalTheory.CyclicNormCheck.real_clause_iff {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ] [CharZero F]
    [Module.Finite F E] [IsGalois F E] {x : F} (hx : x ≠ 0) :
    ((¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ) → 0 < algebraMap F ℝ x) ↔
      ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = algebraMap F ℝ x := by sorry
