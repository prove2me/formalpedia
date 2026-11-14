-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg122
-- name    : OAI.UniversalTensorSquare.sg122
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T20:51:57.246534+00:00
-- url     : https://prove2.me/theorems/1a3113cd-0590-4ea5-b66e-1890ffac1a43
-- title:
--   OAI.UniversalTensorSquare.sg122: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg122` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg122 : RowSquare [2,2,1,1,1] [7]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree20_13All`, `OAI.UniversalTensorSquare.degreeTree20_2All`, `OAI.UniversalTensorSquare.degreeTree20_9All`, `OAI.UniversalTensorSquare.degreeTree22_12All`, `OAI.UniversalTensorSquare.degreeTree22_4All`, `OAI.UniversalTensorSquare.degreeTree22_6All`, `OAI.UniversalTensorSquare.degreeTree22_9All`, `OAI.UniversalTensorSquare.degreeTree24_14All`, `OAI.UniversalTensorSquare.degreeTree24_17All`, `OAI.UniversalTensorSquare.degreeTree24_19All`, `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree24_21All`, `OAI.UniversalTensorSquare.degreeTree24_23All`, `OAI.UniversalTensorSquare.degreeTree24_27All`, `OAI.UniversalTensorSquare.degreeTree24_3All`, `OAI.UniversalTensorSquare.degreeTree24_8All`, `OAI.UniversalTensorSquare.degreeTree26_19All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_26All`, `OAI.UniversalTensorSquare.degreeTree26_37All`, `OAI.UniversalTensorSquare.degreeTree26_56All`, `OAI.UniversalTensorSquare.degreeTree26_57All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree35_10All`, `OAI.UniversalTensorSquare.degreeTree35_14All`, `OAI.UniversalTensorSquare.degreeTree35_16All`, `OAI.UniversalTensorSquare.degreeTree35_8All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_55All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_83All`, `OAI.UniversalTensorSquare.degreeTree39_87All`, `OAI.UniversalTensorSquare.degreeTree43_309All`, `OAI.UniversalTensorSquare.degree_pos24`, `OAI.UniversalTensorSquare.sg10976`, `OAI.UniversalTensorSquare.sg10994`, `OAI.UniversalTensorSquare.sg11917`, `OAI.UniversalTensorSquare.sg11938`, `OAI.UniversalTensorSquare.sg11962`, `OAI.UniversalTensorSquare.sg11977`, `OAI.UniversalTensorSquare.sg12028`, `OAI.UniversalTensorSquare.sg12070`, `OAI.UniversalTensorSquare.sg12087`, `OAI.UniversalTensorSquare.sg12092`, `OAI.UniversalTensorSquare.sg12122`, `OAI.UniversalTensorSquare.sg12218`, `OAI.UniversalTensorSquare.sg13039`, `OAI.UniversalTensorSquare.sg13168`, `OAI.UniversalTensorSquare.sg13386`, `OAI.UniversalTensorSquare.sg13467`, `OAI.UniversalTensorSquare.sg21442`, `OAI.UniversalTensorSquare.sg21458`, `OAI.UniversalTensorSquare.sg21468`, `OAI.UniversalTensorSquare.sg21469`, `OAI.UniversalTensorSquare.sg21478`, `OAI.UniversalTensorSquare.sg21493`, `OAI.UniversalTensorSquare.sg21506`, `OAI.UniversalTensorSquare.sg21560`, `OAI.UniversalTensorSquare.sg22497`, `OAI.UniversalTensorSquare.sg22531`, `OAI.UniversalTensorSquare.sg22557`, `OAI.UniversalTensorSquare.sg22570`, `OAI.UniversalTensorSquare.sg22587`, `OAI.UniversalTensorSquare.sg22643`, `OAI.UniversalTensorSquare.sg22676` and `OAI.UniversalTensorSquare.sg22708` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg122)

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

lemma sg122 : RowSquare [2,2,1,1,1] [7] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
