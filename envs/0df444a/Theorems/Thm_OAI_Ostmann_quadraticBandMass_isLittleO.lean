-- Prove2me | Theorems.Thm_OAI_Ostmann_quadraticBandMass_isLittleO
-- name    : OAI.Ostmann.quadraticBandMass_isLittleO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:15:17.769907+00:00
-- url     : https://prove2.me/theorems/6cf15052-2e77-45bc-a485-d989fffb2952
-- title:
--   OAI.Ostmann.quadraticBandMass_isLittleO: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.quadraticBandMass_isLittleO` of [lean/OAI/NumberTheory/Ostmann/QuadraticCenter/MaximalQuadraticBias.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/QuadraticCenter/MaximalQuadraticBias.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical`):
--
--   ```lean
--   theorem quadraticBandMass_isLittleO
--       (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
--       (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
--       (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
--       {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
--       (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
--       (C₀ : ℝ) (hM : MertensEstimate C₀)
--       (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
--       (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
--       (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
--       (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0) :
--       (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.PublishedBonamiBound`, `OAI.Ostmann.PublishedQuadraticLargeSieve`, `OAI.Ostmann.PublishedSummandSizeBound` and `OAI.Ostmann.tailResidues` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.negTailResidues` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedRealZeroInput` and `OAI.Ostmann.PublishedSiegelBound` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.quadraticBandMass` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.EventuallyPrimeSumset.initial_broad_prior_centers` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/QuadraticCenter/MaximalQuadraticBias.lean (declaration OAI.Ostmann.quadraticBandMass_isLittleO)

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D005

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem quadraticBandMass_isLittleO
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C₀ : ℝ) (hM : MertensEstimate C₀)
    (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0) :
    (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  sorry

end Ostmann

end OAI
end
