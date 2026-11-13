-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg61
-- name    : OAI.UniversalTensorSquare.sg61
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:24:01.939209+00:00
-- url     : https://prove2.me/theorems/330304c8-dd4a-4105-8dc9-e4857f953272
-- title:
--   OAI.UniversalTensorSquare.sg61: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg61` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg61 : RowSquare [2,2,1,1] [6]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree20_13All`, `OAI.UniversalTensorSquare.degreeTree20_2All`, `OAI.UniversalTensorSquare.degreeTree20_3All`, `OAI.UniversalTensorSquare.degreeTree20_4All`, `OAI.UniversalTensorSquare.degreeTree20_8All`, `OAI.UniversalTensorSquare.degreeTree20_9All`, `OAI.UniversalTensorSquare.degreeTree22_10All`, `OAI.UniversalTensorSquare.degreeTree22_12All`, `OAI.UniversalTensorSquare.degreeTree22_1All`, `OAI.UniversalTensorSquare.degreeTree22_4All`, `OAI.UniversalTensorSquare.degreeTree22_5All`, `OAI.UniversalTensorSquare.degreeTree22_6All`, `OAI.UniversalTensorSquare.degreeTree22_8All`, `OAI.UniversalTensorSquare.degreeTree22_9All`, `OAI.UniversalTensorSquare.degreeTree24_12All`, `OAI.UniversalTensorSquare.degreeTree24_14All`, `OAI.UniversalTensorSquare.degreeTree24_17All`, `OAI.UniversalTensorSquare.degreeTree24_22All`, `OAI.UniversalTensorSquare.degreeTree26_11All`, `OAI.UniversalTensorSquare.degreeTree26_15All`, `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_19All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_35All`, `OAI.UniversalTensorSquare.degreeTree26_37All`, `OAI.UniversalTensorSquare.degreeTree26_38All`, `OAI.UniversalTensorSquare.degreeTree26_39All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degreeTree26_42All`, `OAI.UniversalTensorSquare.degreeTree26_47All`, `OAI.UniversalTensorSquare.degreeTree26_50All`, `OAI.UniversalTensorSquare.degreeTree26_53All`, `OAI.UniversalTensorSquare.degreeTree26_56All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree31_0All`, `OAI.UniversalTensorSquare.degreeTree35_14All`, `OAI.UniversalTensorSquare.degreeTree35_8All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree43_640All`, `OAI.UniversalTensorSquare.degreeTreeAll16`, `OAI.UniversalTensorSquare.degreeTreeAll18`, `OAI.UniversalTensorSquare.degreeTreeAll22`, `OAI.UniversalTensorSquare.sg21446`, `OAI.UniversalTensorSquare.sg5708` and `OAI.UniversalTensorSquare.sg5709` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg61)

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

lemma sg61 : RowSquare [2,2,1,1] [6] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
