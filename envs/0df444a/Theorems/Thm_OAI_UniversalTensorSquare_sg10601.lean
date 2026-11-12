-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg10601
-- name    : OAI.UniversalTensorSquare.sg10601
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:31:47.158767+00:00
-- url     : https://prove2.me/theorems/d0d9a9d9-dea7-4585-ba27-bdd5ec35e7eb
-- title:
--   OAI.UniversalTensorSquare.sg10601: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg10601` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes25.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes25.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg10601 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_21All`, `OAI.UniversalTensorSquare.degreeTree43_24All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.sg23749`, `OAI.UniversalTensorSquare.sg23750`, `OAI.UniversalTensorSquare.sg23826`, `OAI.UniversalTensorSquare.sg23893`, `OAI.UniversalTensorSquare.sg23941`, `OAI.UniversalTensorSquare.sg23964`, `OAI.UniversalTensorSquare.sg23971`, `OAI.UniversalTensorSquare.sg23980`, `OAI.UniversalTensorSquare.sg24202`, `OAI.UniversalTensorSquare.sg24334` and `OAI.UniversalTensorSquare.sg25427` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes25.lean (declaration OAI.UniversalTensorSquare.sg10601)

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

lemma sg10601 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
