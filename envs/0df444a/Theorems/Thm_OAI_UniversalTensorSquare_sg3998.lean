-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3998
-- name    : OAI.UniversalTensorSquare.sg3998
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T18:43:02.798484+00:00
-- url     : https://prove2.me/theorems/d0db0fbd-c1ab-4cf6-b069-833e59207466
-- title:
--   OAI.UniversalTensorSquare.sg3998: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3998` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3998 : RowSquare [5,5,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree41_4All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.degreeTree43_84All`, `OAI.UniversalTensorSquare.sg10911`, `OAI.UniversalTensorSquare.sg12910`, `OAI.UniversalTensorSquare.sg12983`, `OAI.UniversalTensorSquare.sg12990`, `OAI.UniversalTensorSquare.sg13012`, `OAI.UniversalTensorSquare.sg13064`, `OAI.UniversalTensorSquare.sg13206`, `OAI.UniversalTensorSquare.sg13214`, `OAI.UniversalTensorSquare.sg13239`, `OAI.UniversalTensorSquare.sg13357`, `OAI.UniversalTensorSquare.sg13364`, `OAI.UniversalTensorSquare.sg13438`, `OAI.UniversalTensorSquare.sg13475`, `OAI.UniversalTensorSquare.sg23506`, `OAI.UniversalTensorSquare.sg23557`, `OAI.UniversalTensorSquare.sg23565`, `OAI.UniversalTensorSquare.sg23571`, `OAI.UniversalTensorSquare.sg23598`, `OAI.UniversalTensorSquare.sg23604`, `OAI.UniversalTensorSquare.sg25092`, `OAI.UniversalTensorSquare.sg25104`, `OAI.UniversalTensorSquare.sg25913`, `OAI.UniversalTensorSquare.sg26306`, `OAI.UniversalTensorSquare.sg26555`, `OAI.UniversalTensorSquare.sg26782`, `OAI.UniversalTensorSquare.sg27036`, `OAI.UniversalTensorSquare.sg27145`, `OAI.UniversalTensorSquare.sg28680`, `OAI.UniversalTensorSquare.sg28877`, `OAI.UniversalTensorSquare.sg29541`, `OAI.UniversalTensorSquare.sg30135`, `OAI.UniversalTensorSquare.sg30726`, `OAI.UniversalTensorSquare.sg30764`, `OAI.UniversalTensorSquare.sg31129`, `OAI.UniversalTensorSquare.sg7256` and `OAI.UniversalTensorSquare.sg7269` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg3998)

import Mathlib
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3998 : RowSquare [5,5,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
