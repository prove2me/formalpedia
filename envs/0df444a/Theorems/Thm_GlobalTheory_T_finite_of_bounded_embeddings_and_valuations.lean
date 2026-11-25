-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_of_bounded_embeddings_and_valuations
-- name    : GlobalTheory.T.finite_of_bounded_embeddings_and_valuations
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:01.242713+00:00
-- url     : https://prove2.me/theorems/2f7e0139-7487-5f1d-ad73-bd3e252cb679
-- title:
--   T: finite of bounded embeddings and valuations
-- statement:
--   The T construction uses the finite of bounded embeddings and valuations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfBoundedEmbeddingsAndValuationsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfBoundedEmbeddingsAndValuationsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuationsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_of_bounded_embeddings_and_valuations : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by sorry
