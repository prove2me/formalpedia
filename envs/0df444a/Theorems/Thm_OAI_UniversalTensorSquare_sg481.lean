-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg481
-- name    : OAI.UniversalTensorSquare.sg481
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:35:15.890191+00:00
-- url     : https://prove2.me/theorems/5d894f48-152c-45d8-9e9a-58859218e3d6
-- title:
--   OAI.UniversalTensorSquare.sg481: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg481` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg481 : RowSquare [3,2,2,2] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.sg33227`, `OAI.UniversalTensorSquare.sg36210`, `OAI.UniversalTensorSquare.sg36211`, `OAI.UniversalTensorSquare.sg36212`, `OAI.UniversalTensorSquare.sg36984`, `OAI.UniversalTensorSquare.sg37358`, `OAI.UniversalTensorSquare.sg37571`, `OAI.UniversalTensorSquare.sg37573`, `OAI.UniversalTensorSquare.sg37574`, `OAI.UniversalTensorSquare.sg37630`, `OAI.UniversalTensorSquare.sg37664`, `OAI.UniversalTensorSquare.sg38293`, `OAI.UniversalTensorSquare.sg38661`, `OAI.UniversalTensorSquare.sg39437`, `OAI.UniversalTensorSquare.sg40713`, `OAI.UniversalTensorSquare.sg40735`, `OAI.UniversalTensorSquare.sg41139`, `OAI.UniversalTensorSquare.sg41151`, `OAI.UniversalTensorSquare.sg41268`, `OAI.UniversalTensorSquare.sg41359`, `OAI.UniversalTensorSquare.sg41482`, `OAI.UniversalTensorSquare.sg41490`, `OAI.UniversalTensorSquare.sg41492` and `OAI.UniversalTensorSquare.sg41927` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg481)

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

lemma sg481 : RowSquare [3,2,2,2] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
