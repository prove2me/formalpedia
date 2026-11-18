-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg378
-- name    : OAI.UniversalTensorSquare.sg378
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T15:06:16.097764+00:00
-- url     : https://prove2.me/theorems/3d330275-c395-4385-a86c-8876ec60bbd0
-- title:
--   OAI.UniversalTensorSquare.sg378: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg378` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg378 : RowSquare [5,1,1,1] [3,3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_461All`, `OAI.UniversalTensorSquare.degreeTree43_507All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_590All`, `OAI.UniversalTensorSquare.degreeTree43_633All`, `OAI.UniversalTensorSquare.degreeTree43_86All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree62_537All`, `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.sg10376`, `OAI.UniversalTensorSquare.sg10500`, `OAI.UniversalTensorSquare.sg15945`, `OAI.UniversalTensorSquare.sg24937`, `OAI.UniversalTensorSquare.sg25001`, `OAI.UniversalTensorSquare.sg26339`, `OAI.UniversalTensorSquare.sg26583`, `OAI.UniversalTensorSquare.sg26608`, `OAI.UniversalTensorSquare.sg27354`, `OAI.UniversalTensorSquare.sg30493`, `OAI.UniversalTensorSquare.sg31106`, `OAI.UniversalTensorSquare.sg31563`, `OAI.UniversalTensorSquare.sg31749`, `OAI.UniversalTensorSquare.sg38577`, `OAI.UniversalTensorSquare.sg39731`, `OAI.UniversalTensorSquare.sg41665`, `OAI.UniversalTensorSquare.sg41891`, `OAI.UniversalTensorSquare.sg41897`, `OAI.UniversalTensorSquare.sg42177`, `OAI.UniversalTensorSquare.sg42625`, `OAI.UniversalTensorSquare.sg42638`, `OAI.UniversalTensorSquare.sg42687`, `OAI.UniversalTensorSquare.sg42733`, `OAI.UniversalTensorSquare.sg4956`, `OAI.UniversalTensorSquare.sg525`, `OAI.UniversalTensorSquare.sg5633`, `OAI.UniversalTensorSquare.sg7216`, `OAI.UniversalTensorSquare.sg9968` and `OAI.UniversalTensorSquare.sg9985` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg378)

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

lemma sg378 : RowSquare [5,1,1,1] [3,3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
