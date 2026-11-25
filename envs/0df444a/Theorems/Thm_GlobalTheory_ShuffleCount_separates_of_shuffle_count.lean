-- Prove2me | Theorems.Thm_GlobalTheory_ShuffleCount_separates_of_shuffle_count
-- name    : GlobalTheory.ShuffleCount.separates_of_shuffle_count
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:33.754449+00:00
-- url     : https://prove2.me/theorems/cf1a2fbf-93dc-4767-9852-1c938f1f6d68
-- title:
--   Shuffle Count: separates of shuffle count
-- statement:
--   The Shuffle Count construction uses the separates of shuffle count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ShuffleCountLinearIndependentClasses.lean#L63-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ShuffleCountLinearIndependentClasses.lean#L63-L215

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ShuffleCountLinearIndependentClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory GlobalTheory.ShuffleCount
open MvPolynomial

theorem GlobalTheory.ShuffleCount.separates_of_shuffle_count : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by sorry
