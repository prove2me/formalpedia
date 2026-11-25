-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_of_valuation_bounded_norm_le_one
-- name    : GlobalTheory.T.finite_of_valuation_bounded_norm_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:15.961241+00:00
-- url     : https://prove2.me/theorems/37d516dc-baff-4afa-9f9c-3afe6d4364af
-- title:
--   T: finite of valuation bounded norm le one
-- statement:
--   The T construction uses the finite of valuation bounded norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfValuationBoundedNormLeOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteOfValuationBoundedNormLeOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfValuationBoundedNormLeOneStatement
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

theorem GlobalTheory.T.finite_of_valuation_bounded_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by sorry
