-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_fourPairEmbedding_contract_s50
-- name    : OAI.Laughlin.Fock.fourPairEmbedding_contract_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:58:15.114223+00:00
-- url     : https://prove2.me/theorems/b37bfc00-4633-4a66-8f5a-85374953aa2b
-- title:
--   OAI.Laughlin.Fock.fourPairEmbedding_contract_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.fourPairEmbedding_contract` of [lean/OAI/Analysis/Laughlin/FourBody/PairTarget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/PairTarget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin`, `open scoped BigOperators Matrix Kronecker`):
--
--   ```lean
--   theorem fourPairEmbedding_contract_s50 (Q : ℕ) (hQ : 1 ≤ Q)
--       (j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1)) (x : Space Q) :
--       (∑ i : FourWedgeIndex Q, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x) =
--         sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.SpinIndex` (definitions bundle `OAIQ050L005` of this split); `OAI.Laughlin.Spin.genericCoupledWeight` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Fock.sourcePairEnd`, `OAI.Laughlin.Spin.FourWedgeIndex` and `OAI.Laughlin.Spin.WedgePairIndex` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Spin.fourPairEmbedding` (definitions bundle `OAIQ050L021` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/PairTarget.lean (declaration OAI.Laughlin.Fock.fourPairEmbedding_contract)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix Kronecker

theorem fourPairEmbedding_contract_s50 (Q : ℕ) (hQ : 1 ≤ Q)
    (j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1)) (x : Space Q) :
    (∑ i : FourWedgeIndex Q, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x) =
      sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x) := by
  sorry

end Laughlin.Fock

end OAI
end
