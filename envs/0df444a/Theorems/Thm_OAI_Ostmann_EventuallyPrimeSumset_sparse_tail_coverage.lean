-- Prove2me | Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_coverage
-- name    : OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:20:51.716137+00:00
-- url     : https://prove2.me/theorems/c52779d4-45bb-4270-b940-a08254e8fc60
-- title:
--   OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage` of [lean/OAI/NumberTheory/Ostmann/Characters/SparseTailCoverage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/SparseTailCoverage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators`):
--
--   ```lean
--    theorem EventuallyPrimeSumset.sparse_tail_coverage
--       (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
--       (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
--       (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
--       (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
--       (hPNT : PublishedSmoothPrincipalPNT) (C : ℝ) (hC : 1000 ≤ C) :
--       ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
--         ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
--         ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
--           (S : ∀ i, Finset (ZMod (p i))),
--           Pairwise (fun i j => (p i).Coprime (p j)) →
--           (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
--           (∀ i, (100 : ℝ) ≤ p i) →
--           (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
--           (∀ i, residueDensity (S i) ≤ 2 / 3) →
--           ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
--           (∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2) →
--           (∑ i, (p i : ℝ)⁻¹) ≤ L →
--           (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
--           (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
--           let U := ∏ i, sparseKernelUnitFactor (p i)
--             (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
--           0 < U ∧ ((∫ t : ℝ, primeMeanTest t) / 8) * U * X ≤
--             Real.log X * ∑ a ∈ summandTail A (summandTailCutoff (Real.exp L)) X,
--               ∑ b ∈ summandTail B (summandTailCutoff (Real.exp L)) X,
--                 sparseSubsetWeight p S (sparseTruncationDegree C L)
--                   (fun i => ((a + b : ℕ) : ZMod (p i)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.ComplexZeroEnumeration` and `OAI.Ostmann.PrimitiveComplexCharacter` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.PublishedSmoothPrincipalPNT`, `OAI.Ostmann.PublishedSummandSizeBound`, `OAI.Ostmann.primeMeanTest`, `OAI.Ostmann.residueDensity`, `OAI.Ostmann.summandTail` and `OAI.Ostmann.summandTailCutoff` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.largeTransformSpectrum`, `OAI.Ostmann.sparseKernelUnitFactor` and `OAI.Ostmann.sparseTruncationDegree` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedComplexZeroDensity`, `OAI.Ostmann.PublishedComplexZeroRegion` and `OAI.Ostmann.PublishedSmoothExplicitFormula` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.sparseSubsetWeight` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/SparseTailCoverage.lean (declaration OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage)

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.sparse_tail_coverage
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) (C : ℝ) (hC : 1000 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
        (∀ i, (100 : ℝ) ≤ p i) →
        (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
        (∀ i, residueDensity (S i) ≤ 2 / 3) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
        (∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        let U := ∏ i, sparseKernelUnitFactor (p i)
          (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
        0 < U ∧ ((∫ t : ℝ, primeMeanTest t) / 8) * U * X ≤
          Real.log X * ∑ a ∈ summandTail A (summandTailCutoff (Real.exp L)) X,
            ∑ b ∈ summandTail B (summandTailCutoff (Real.exp L)) X,
              sparseSubsetWeight p S (sparseTruncationDegree C L)
                (fun i => ((a + b : ℕ) : ZMod (p i))) := by
  sorry

end Ostmann

end OAI
end
