-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_PrimeRead_read_in_field
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.read_in_field
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:34.946783+00:00
-- url     : https://prove2.me/theorems/1089c29f-e6c4-5baf-84ae-ddf41017544b
-- title:
--   Prime Read: read in field
-- statement:
--   The Prime Read construction uses the read in field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L42-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/BoundaryOnPrimes.lean#L42-L97

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.read_in_field {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω)
    (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ)
    (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ)
    (hF : aeval τ F ≠ 0) (hS : S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)))
    (hz : ∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i))
    (hprime : ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (𝔮 : Ideal (MvPolynomial σ ℂ))
    (hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮)
    (hFq : map (algebraMap ℚ ℂ) F ∉ 𝔮)
    (E : Type) [Field E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮) :
    (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by sorry
