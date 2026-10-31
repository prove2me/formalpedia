-- Prove2me | Theorems.Thm_OAI_Ostmann_twoInfiniteSummandsImpossible_without_summand_size
-- name    : OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:17:57.367285+00:00
-- url     : https://prove2.me/theorems/ec610791-bfa2-46ce-9793-896bcbf499e5
-- title:
--   OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size` of [lean/OAI/NumberTheory/Ostmann/MainWithoutSummandSize.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/MainWithoutSummandSize.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`):
--
--   ```lean
--   theorem twoInfiniteSummandsImpossible_without_summand_size
--       (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
--       (hD : PublishedComplexZeroDensity actualCharacterZeros) :
--       TwoInfiniteSummandsImpossible
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.actualCharacterZeros` (definitions bundle `OAIQ095D000` of this split); `OAI.Ostmann.PublishedQuadraticLargeSieve` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.PublishedComplexZeroDensity` and `OAI.Ostmann.PublishedSiegelBound` (definitions bundle `OAIQ095D003` of this split); `OAI.Ostmann.TwoInfiniteSummandsImpossible` (the published bundle `Def_OstmannComplete`).
--
--   **Used by.** The proof of `OAI.Ostmann.twoInfiniteSummandsImpossible` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/MainWithoutSummandSize.lean (declaration OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size)

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

theorem twoInfiniteSummandsImpossible_without_summand_size
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible := by
  sorry

end Ostmann

end OAI
end
