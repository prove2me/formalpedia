-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_boundary_on_primes
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.boundary_on_primes
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:47.999055+00:00
-- url     : https://prove2.me/theorems/dbf87db2-8626-4e71-8f0f-a5fc050e26de
-- title:
--   Prime Read: boundary on primes
-- statement:
--   The Prime Read construction uses the boundary on primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L99-L111

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_BoundaryOnPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.boundary_on_primes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → ∀ 𝔮 : Ideal (MvPolynomial σ ℂ), 𝔮.IsPrime → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮) → map (algebraMap ℚ ℂ) F ∉ 𝔮 → ((∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮) := by sorry
