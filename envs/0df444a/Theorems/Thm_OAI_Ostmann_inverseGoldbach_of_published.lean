-- Prove2me | Theorems.Thm_OAI_Ostmann_inverseGoldbach_of_published
-- name    : OAI.Ostmann.inverseGoldbach_of_published
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:02.834296+00:00
-- url     : https://prove2.me/theorems/e0ef6d32-66d1-4d37-bbac-be8a2d75f11a
-- title:
--   OAI.Ostmann.inverseGoldbach_of_published: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.inverseGoldbach_of_published` of [lean/OAI/NumberTheory/Ostmann/InverseGoldbach.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/InverseGoldbach.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`):
--
--   ```lean
--   theorem inverseGoldbach_of_published
--       (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
--       (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
--       (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
--       (sieve : PublishedQuadraticLargeSieve)
--       (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
--       (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
--       (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
--       (hPNT : PublishedSmoothPrincipalPNT) : InverseGoldbach
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.ComplexZeroEnumeration` and `OAI.Ostmann.PrimitiveComplexCharacter` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.MertensEstimate`, `OAI.Ostmann.MertensHarmonicEstimate`, `OAI.Ostmann.PublishedAdditiveLargeSieve`, `OAI.Ostmann.PublishedBonamiBound`, `OAI.Ostmann.PublishedQuadraticLargeSieve`, `OAI.Ostmann.PublishedSmoothPrincipalPNT` and `OAI.Ostmann.PublishedSummandSizeBound` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.PublishedComplexZeroDensity`, `OAI.Ostmann.PublishedComplexZeroRegion`, `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedRealZeroInput`, `OAI.Ostmann.PublishedSiegelBound` and `OAI.Ostmann.PublishedSmoothExplicitFormula` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.InverseGoldbach` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.inverseGoldbach_without_summand_size` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/InverseGoldbach.lean (declaration OAI.Ostmann.inverseGoldbach_of_published)

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D003

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

theorem inverseGoldbach_of_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) : InverseGoldbach := by
  sorry

end Ostmann

end OAI
end
