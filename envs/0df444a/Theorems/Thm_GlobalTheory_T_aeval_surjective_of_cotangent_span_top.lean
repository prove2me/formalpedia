-- Prove2me | Theorems.Thm_GlobalTheory_T_aeval_surjective_of_cotangent_span_top
-- name    : GlobalTheory.T.aeval_surjective_of_cotangent_span_top
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:45.605775+00:00
-- url     : https://prove2.me/theorems/312a395a-95f5-4efa-a7a4-ea213a1e56fd
-- title:
--   T: aeval surjective of cotangent span top
-- statement:
--   The T construction uses the aeval surjective of cotangent span top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AevalSurjectiveOfCotangentSpanTopStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AevalSurjectiveOfCotangentSpanTopStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalSurjectiveOfCotangentSpanTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalSurjectiveOfCotangentSpanTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.aeval_surjective_of_cotangent_span_top : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by sorry
