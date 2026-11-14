-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1650
-- name    : OAI.UniversalTensorSquare.sg1650
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T21:26:29.579885+00:00
-- url     : https://prove2.me/theorems/bd88bef5-5713-46a3-8482-0db5b43a14b3
-- title:
--   OAI.UniversalTensorSquare.sg1650: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1650` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1650 : RowSquare [4,4,2,2] [1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree20_13All`, `OAI.UniversalTensorSquare.degreeTree20_2All`, `OAI.UniversalTensorSquare.degreeTree20_9All`, `OAI.UniversalTensorSquare.degreeTree22_10All`, `OAI.UniversalTensorSquare.degreeTree22_12All`, `OAI.UniversalTensorSquare.degreeTree22_1All`, `OAI.UniversalTensorSquare.degreeTree22_5All`, `OAI.UniversalTensorSquare.degreeTree22_6All`, `OAI.UniversalTensorSquare.degreeTree22_8All`, `OAI.UniversalTensorSquare.degreeTree22_9All`, `OAI.UniversalTensorSquare.degreeTree24_11All`, `OAI.UniversalTensorSquare.degreeTree24_14All`, `OAI.UniversalTensorSquare.degreeTree24_17All`, `OAI.UniversalTensorSquare.degreeTree24_19All`, `OAI.UniversalTensorSquare.degreeTree24_22All`, `OAI.UniversalTensorSquare.degreeTree24_23All`, `OAI.UniversalTensorSquare.degreeTree24_27All`, `OAI.UniversalTensorSquare.degreeTree24_5All`, `OAI.UniversalTensorSquare.degreeTree26_10All`, `OAI.UniversalTensorSquare.degreeTree26_11All`, `OAI.UniversalTensorSquare.degreeTree26_15All`, `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_21All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_32All`, `OAI.UniversalTensorSquare.degreeTree26_35All`, `OAI.UniversalTensorSquare.degreeTree26_38All`, `OAI.UniversalTensorSquare.degreeTree26_39All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degreeTree26_46All`, `OAI.UniversalTensorSquare.degreeTree26_47All`, `OAI.UniversalTensorSquare.degreeTree26_50All`, `OAI.UniversalTensorSquare.degreeTree26_56All`, `OAI.UniversalTensorSquare.degreeTree26_57All`, `OAI.UniversalTensorSquare.degreeTree26_58All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree26_7All`, `OAI.UniversalTensorSquare.degreeTree35_12All`, `OAI.UniversalTensorSquare.degreeTree35_22All`, `OAI.UniversalTensorSquare.degreeTree35_8All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_54All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree43_116All`, `OAI.UniversalTensorSquare.degreeTreeAll18`, `OAI.UniversalTensorSquare.sg12283`, `OAI.UniversalTensorSquare.sg12310`, `OAI.UniversalTensorSquare.sg12314`, `OAI.UniversalTensorSquare.sg12325`, `OAI.UniversalTensorSquare.sg12327`, `OAI.UniversalTensorSquare.sg12330`, `OAI.UniversalTensorSquare.sg13452`, `OAI.UniversalTensorSquare.sg13485`, `OAI.UniversalTensorSquare.sg13488`, `OAI.UniversalTensorSquare.sg13494`, `OAI.UniversalTensorSquare.sg13496`, `OAI.UniversalTensorSquare.sg21439`, `OAI.UniversalTensorSquare.sg21455`, `OAI.UniversalTensorSquare.sg21483`, `OAI.UniversalTensorSquare.sg21530` and `OAI.UniversalTensorSquare.sg22765` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg1650)

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

lemma sg1650 : RowSquare [4,4,2,2] [1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
