-- Prove2me | Theorems.Thm_GlobalTheory_BddFinite_finite_of_bdd
-- name    : GlobalTheory.BddFinite.finite_of_bdd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:16.175416+00:00
-- url     : https://prove2.me/theorems/4a207e04-2a71-428d-a309-5cfa6c278201
-- title:
--   Bdd Finite: finite of bdd
-- statement:
--   The Bdd Finite construction uses the finite of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfBoundedEmbeddingsAndValuations.lean#L31-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfBoundedEmbeddingsAndValuations.lean#L31-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BddFinite

theorem GlobalTheory.BddFinite.finite_of_bdd : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by sorry
