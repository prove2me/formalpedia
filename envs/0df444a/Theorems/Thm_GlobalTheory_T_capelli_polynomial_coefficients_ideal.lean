-- Prove2me | Theorems.Thm_GlobalTheory_T_capelli_polynomial_coefficients_ideal
-- name    : GlobalTheory.T.capelli_polynomial_coefficients_ideal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:53.006005+00:00
-- url     : https://prove2.me/theorems/14b13e21-1aac-4c0c-9441-27cd6df3062e
-- title:
--   T: capelli polynomial coefficients ideal
-- statement:
--   The T construction uses the capelli polynomial coefficients ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdealStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdealStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdealStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.capelli_polynomial_coefficients_ideal : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D R S : ℂ → Module.End ℂ V) (Wn I : Submodule ℂ V) (W₀ : Set V) (c₁ c₂ : ℂ) (n₁ n₂ : ℕ) (a b : ℕ → Module.End ℂ V), (∀ u v, Commute (R u) (R v)) → (∀ u v, Commute (R u) (S v)) → (∀ u v, Commute (S u) (S v)) → (∀ u, ∀ F ∈ Wn, D u F ∈ Wn) → (∀ u, ∀ F ∈ I, R u F ∈ I) → (∀ u, ∀ F ∈ I, S u F ∈ I) → (∀ u, ∀ F ∈ Wn, D u F - S (u + c₂) (R (u + c₁) F) ∈ I) → a n₁ = 1 → (∀ k, a k ∈ Submodule.span ℂ (Set.range R)) → (∀ u : ℂ, R u = ∑ k ∈ Finset.range (n₁ + 1), u ^ k • a k) → b n₂ = 1 → (∀ k, b k ∈ Submodule.span ℂ (Set.range S)) → (∀ u : ℂ, S u = ∑ k ∈ Finset.range (n₂ + 1), u ^ k • b k) → W₀ ⊆ Wn → (∀ u, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (D u) p F = 0) → (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (R u) q F ∈ I) ∧ ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (S u) q F ∈ I := by sorry
