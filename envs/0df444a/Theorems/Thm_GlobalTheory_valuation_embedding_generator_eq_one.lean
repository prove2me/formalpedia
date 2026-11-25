-- Prove2me | Theorems.Thm_GlobalTheory_valuation_embedding_generator_eq_one
-- name    : GlobalTheory.valuation_embedding_generator_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:07.279025+00:00
-- url     : https://prove2.me/theorems/162ec1c9-4516-4912-99ed-65f4a97449a9
-- title:
--   Global Theory: valuation embedding generator eq one
-- statement:
--   The Global Theory construction uses the valuation embedding generator eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationEmbeddingGeneratorEqOne.lean#L19-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationEmbeddingGeneratorEqOne.lean#L19-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.valuation_embedding_generator_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
      ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h →
      ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by sorry
