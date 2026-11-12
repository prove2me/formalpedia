-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20423
-- name    : OAI.UniversalTensorSquare.sg20423
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:50:48.847286+00:00
-- url     : https://prove2.me/theorems/7ba06049-187d-4810-b2f2-389a9ba23fbb
-- title:
--   OAI.UniversalTensorSquare.sg20423: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20423` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20423 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_102All`, `OAI.UniversalTensorSquare.degreeTree62_110All`, `OAI.UniversalTensorSquare.degreeTree62_120All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_150All`, `OAI.UniversalTensorSquare.degreeTree62_151All`, `OAI.UniversalTensorSquare.degreeTree62_164All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_22All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_270All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_297All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.degreeTree62_98All`, `OAI.UniversalTensorSquare.sg32363`, `OAI.UniversalTensorSquare.sg32376`, `OAI.UniversalTensorSquare.sg32387`, `OAI.UniversalTensorSquare.sg32418`, `OAI.UniversalTensorSquare.sg32427`, `OAI.UniversalTensorSquare.sg32460`, `OAI.UniversalTensorSquare.sg32728`, `OAI.UniversalTensorSquare.sg33088`, `OAI.UniversalTensorSquare.sg33180`, `OAI.UniversalTensorSquare.sg33302`, `OAI.UniversalTensorSquare.sg33313`, `OAI.UniversalTensorSquare.sg33347`, `OAI.UniversalTensorSquare.sg33378`, `OAI.UniversalTensorSquare.sg33739`, `OAI.UniversalTensorSquare.sg34040`, `OAI.UniversalTensorSquare.sg34064`, `OAI.UniversalTensorSquare.sg34135`, `OAI.UniversalTensorSquare.sg34167`, `OAI.UniversalTensorSquare.sg34191`, `OAI.UniversalTensorSquare.sg34225`, `OAI.UniversalTensorSquare.sg34256`, `OAI.UniversalTensorSquare.sg34326`, `OAI.UniversalTensorSquare.sg34401`, `OAI.UniversalTensorSquare.sg34425`, `OAI.UniversalTensorSquare.sg34626`, `OAI.UniversalTensorSquare.sg34640`, `OAI.UniversalTensorSquare.sg34648`, `OAI.UniversalTensorSquare.sg34709`, `OAI.UniversalTensorSquare.sg34754`, `OAI.UniversalTensorSquare.sg34758`, `OAI.UniversalTensorSquare.sg34771`, `OAI.UniversalTensorSquare.sg34841`, `OAI.UniversalTensorSquare.sg34882`, `OAI.UniversalTensorSquare.sg34893`, `OAI.UniversalTensorSquare.sg35007`, `OAI.UniversalTensorSquare.sg35033`, `OAI.UniversalTensorSquare.sg35042`, `OAI.UniversalTensorSquare.sg35069`, `OAI.UniversalTensorSquare.sg35139`, `OAI.UniversalTensorSquare.sg35164`, `OAI.UniversalTensorSquare.sg35173`, `OAI.UniversalTensorSquare.sg35194`, `OAI.UniversalTensorSquare.sg35216`, `OAI.UniversalTensorSquare.sg35309`, `OAI.UniversalTensorSquare.sg37461`, `OAI.UniversalTensorSquare.sg37502`, `OAI.UniversalTensorSquare.sg38604`, `OAI.UniversalTensorSquare.sg38734`, `OAI.UniversalTensorSquare.sg38760`, `OAI.UniversalTensorSquare.sg39382`, `OAI.UniversalTensorSquare.sg39743`, `OAI.UniversalTensorSquare.sg39827`, `OAI.UniversalTensorSquare.sg39848`, `OAI.UniversalTensorSquare.sg39866` and `OAI.UniversalTensorSquare.sg40101` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20423)

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

lemma sg20423 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
