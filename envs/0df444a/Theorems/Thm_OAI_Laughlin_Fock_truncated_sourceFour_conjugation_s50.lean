-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_truncated_sourceFour_conjugation_s50
-- name    : OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:56:01.161791+00:00
-- url     : https://prove2.me/theorems/568cc4c4-b272-42c8-a25b-5e7dc4f790d7
-- title:
--   OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.truncated_sourceFour_conjugation` of [lean/OAI/Analysis/Laughlin/Operators/TruncatedConjugation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/TruncatedConjugation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`):
--
--   ```lean
--   theorem truncated_sourceFour_conjugation_s50 (L Q p : ℕ) (hQ : 0 < Q)
--       (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (j k : Fin (Q+1))
--       (hjL : j.val ≤ L) (hkL : k.val ≤ L) (x : Space Q) :
--       sourceFourEnd Q p j k x =
--         ((pairFactor Q p : ℂ)/((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))) •
--           truncatedScalingInv L Q (limitFourEnd Q p j k (truncatedScaling L Q x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.modeFactor` and `OAI.Laughlin.pairFactor` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.limitFourEnd` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.sourceFourEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.truncatedScaling` and `OAI.Laughlin.Fock.truncatedScalingInv` (definitions bundle `OAIQ050L017` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/TruncatedConjugation.lean (declaration OAI.Laughlin.Fock.truncated_sourceFour_conjugation)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem truncated_sourceFour_conjugation_s50 (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (j k : Fin (Q+1))
    (hjL : j.val ≤ L) (hkL : k.val ≤ L) (x : Space Q) :
    sourceFourEnd Q p j k x =
      ((pairFactor Q p : ℂ)/((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))) •
        truncatedScalingInv L Q (limitFourEnd Q p j k (truncatedScaling L Q x)) := by
  sorry

end Laughlin.Fock

end OAI
end
