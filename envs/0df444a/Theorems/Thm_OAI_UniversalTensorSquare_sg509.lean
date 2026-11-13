-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg509
-- name    : OAI.UniversalTensorSquare.sg509
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:19:19.635264+00:00
-- url     : https://prove2.me/theorems/10b06ed6-b25d-4852-a81b-89f7acb2bfaa
-- title:
--   OAI.UniversalTensorSquare.sg509: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg509` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg509 : RowSquare [3,3,1,1,1] [9]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree20_2All`, `OAI.UniversalTensorSquare.degreeTree22_10All`, `OAI.UniversalTensorSquare.degreeTree22_1All`, `OAI.UniversalTensorSquare.degreeTree22_6All`, `OAI.UniversalTensorSquare.degreeTree22_9All`, `OAI.UniversalTensorSquare.degreeTree24_19All`, `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree24_27All`, `OAI.UniversalTensorSquare.degreeTree24_8All`, `OAI.UniversalTensorSquare.degreeTree26_10All`, `OAI.UniversalTensorSquare.degreeTree26_21All`, `OAI.UniversalTensorSquare.degreeTree26_26All`, `OAI.UniversalTensorSquare.degreeTree26_27All`, `OAI.UniversalTensorSquare.degreeTree26_33All`, `OAI.UniversalTensorSquare.degreeTree26_34All`, `OAI.UniversalTensorSquare.degreeTree26_38All`, `OAI.UniversalTensorSquare.degreeTree26_46All`, `OAI.UniversalTensorSquare.degreeTree26_47All`, `OAI.UniversalTensorSquare.degreeTree26_50All`, `OAI.UniversalTensorSquare.degreeTree26_53All`, `OAI.UniversalTensorSquare.degreeTree26_56All`, `OAI.UniversalTensorSquare.degreeTree26_57All`, `OAI.UniversalTensorSquare.degreeTree26_5All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree26_6All`, `OAI.UniversalTensorSquare.degreeTree26_9All`, `OAI.UniversalTensorSquare.degreeTree35_7All`, `OAI.UniversalTensorSquare.degreeTree39_104All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_560All`, `OAI.UniversalTensorSquare.degree_pos24`, `OAI.UniversalTensorSquare.sg11909`, `OAI.UniversalTensorSquare.sg11932`, `OAI.UniversalTensorSquare.sg11955`, `OAI.UniversalTensorSquare.sg12010`, `OAI.UniversalTensorSquare.sg12062`, `OAI.UniversalTensorSquare.sg12085`, `OAI.UniversalTensorSquare.sg12155`, `OAI.UniversalTensorSquare.sg12176`, `OAI.UniversalTensorSquare.sg12198`, `OAI.UniversalTensorSquare.sg13088`, `OAI.UniversalTensorSquare.sg13240`, `OAI.UniversalTensorSquare.sg13247`, `OAI.UniversalTensorSquare.sg13262`, `OAI.UniversalTensorSquare.sg13358`, `OAI.UniversalTensorSquare.sg13365`, `OAI.UniversalTensorSquare.sg13366`, `OAI.UniversalTensorSquare.sg13476`, `OAI.UniversalTensorSquare.sg13477`, `OAI.UniversalTensorSquare.sg21449`, `OAI.UniversalTensorSquare.sg23433`, `OAI.UniversalTensorSquare.sg23559`, `OAI.UniversalTensorSquare.sg23577`, `OAI.UniversalTensorSquare.sg23594`, `OAI.UniversalTensorSquare.sg25923`, `OAI.UniversalTensorSquare.sg26316`, `OAI.UniversalTensorSquare.sg26556`, `OAI.UniversalTensorSquare.sg30467` and `OAI.UniversalTensorSquare.sg30774` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg509)

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

lemma sg509 : RowSquare [3,3,1,1,1] [9] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
