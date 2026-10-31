-- Prove2me | Theorems.Thm_OAI_Ostmann_EventuallyPrimeSumset_favorable_tail_prime_mass
-- name    : OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:19:31.722609+00:00
-- url     : https://prove2.me/theorems/12a5728f-3211-48af-97a9-2df5fff57d9f
-- title:
--   OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass` of [lean/OAI/NumberTheory/Ostmann/Supply/FavorableTailPrimeMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Supply/FavorableTailPrimeMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem EventuallyPrimeSumset.favorable_tail_prime_mass
--       (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
--       {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
--       (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
--       (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
--       (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
--       (hPNT : PublishedSmoothPrincipalPNT) :
--       ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
--         ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
--           (3 / 20 : ℝ) * L <
--             ∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
--               (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2), (p : ℝ)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.ComplexZeroEnumeration` and `OAI.Ostmann.PrimitiveComplexCharacter` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MertensHarmonicEstimate`, `OAI.Ostmann.PublishedAdditiveLargeSieve`, `OAI.Ostmann.PublishedSmoothPrincipalPNT`, `OAI.Ostmann.PublishedSummandSizeBound`, `OAI.Ostmann.tailResidues` and `OAI.Ostmann.tailSupport` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.favorableTransformPrimes`, `OAI.Ostmann.logLogPrimeBand` and `OAI.Ostmann.negTailResidues` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.PublishedComplexZeroDensity`, `OAI.Ostmann.PublishedComplexZeroRegion` and `OAI.Ostmann.PublishedSmoothExplicitFormula` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.tailFourierMass` (definitions bundle `OAIQ095D007` of this split); `OAI.Ostmann.EventuallyPrimeSumset` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.EventuallyPrimeSumset.constructed_initial_amplitude` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Supply/FavorableTailPrimeMass.lean (declaration OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass)

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

theorem EventuallyPrimeSumset.favorable_tail_prime_mass
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
        (3 / 20 : ℝ) * L <
          ∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
            (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2), (p : ℝ)⁻¹ := by
  sorry

end Ostmann

end OAI
end
