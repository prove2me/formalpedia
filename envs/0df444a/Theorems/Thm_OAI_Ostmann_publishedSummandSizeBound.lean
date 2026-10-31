-- Prove2me | Theorems.Thm_OAI_Ostmann_publishedSummandSizeBound
-- name    : OAI.Ostmann.publishedSummandSizeBound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:01:46.59757+00:00
-- url     : https://prove2.me/theorems/8fc9ade1-a4a6-40a3-bee4-c66f3461bce2
-- title:
--   OAI.Ostmann.publishedSummandSizeBound: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.publishedSummandSizeBound` of [lean/OAI/NumberTheory/Ostmann/Preliminaries/SummandSizeProof.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Preliminaries/SummandSizeProof.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open Filter`):
--
--   ```lean
--    theorem publishedSummandSizeBound : PublishedSummandSizeBound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.PublishedSummandSizeBound` (definitions bundle `OAIQ095D001` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.inverseGoldbach_without_summand_size` and `OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Preliminaries/SummandSizeProof.lean (declaration OAI.Ostmann.publishedSummandSizeBound)

import Mathlib
import Definitions.Def_OAIQ095D001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Filter

 theorem publishedSummandSizeBound : PublishedSummandSizeBound := by
  sorry

end Ostmann

end OAI
end
