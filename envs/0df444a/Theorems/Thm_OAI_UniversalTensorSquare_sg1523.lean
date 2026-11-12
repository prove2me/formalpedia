-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1523
-- name    : OAI.UniversalTensorSquare.sg1523
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:20:56.699342+00:00
-- url     : https://prove2.me/theorems/a98df0d4-04dc-4034-bd8e-5d3bf20e96f0
-- title:
--   OAI.UniversalTensorSquare.sg1523: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1523` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1523 : RowSquare [7,2,1,1] [3,3,3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_129All`, `OAI.UniversalTensorSquare.degreeTree43_159All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_52All`, `OAI.UniversalTensorSquare.degreeTree43_542All`, `OAI.UniversalTensorSquare.degreeTree43_546All`, `OAI.UniversalTensorSquare.degreeTree43_592All`, `OAI.UniversalTensorSquare.degreeTree43_600All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree43_611All`, `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree62_246All`, `OAI.UniversalTensorSquare.degreeTree62_248All`, `OAI.UniversalTensorSquare.degreeTree62_266All`, `OAI.UniversalTensorSquare.degreeTree62_267All`, `OAI.UniversalTensorSquare.degreeTree62_280All`, `OAI.UniversalTensorSquare.degreeTree62_293All`, `OAI.UniversalTensorSquare.sg21857`, `OAI.UniversalTensorSquare.sg21875`, `OAI.UniversalTensorSquare.sg21879`, `OAI.UniversalTensorSquare.sg22071`, `OAI.UniversalTensorSquare.sg22133`, `OAI.UniversalTensorSquare.sg23167`, `OAI.UniversalTensorSquare.sg25123`, `OAI.UniversalTensorSquare.sg25124`, `OAI.UniversalTensorSquare.sg25295`, `OAI.UniversalTensorSquare.sg26665`, `OAI.UniversalTensorSquare.sg26818`, `OAI.UniversalTensorSquare.sg26863`, `OAI.UniversalTensorSquare.sg26876`, `OAI.UniversalTensorSquare.sg26912`, `OAI.UniversalTensorSquare.sg27581`, `OAI.UniversalTensorSquare.sg29802`, `OAI.UniversalTensorSquare.sg29857`, `OAI.UniversalTensorSquare.sg29899`, `OAI.UniversalTensorSquare.sg30338`, `OAI.UniversalTensorSquare.sg30902`, `OAI.UniversalTensorSquare.sg31698`, `OAI.UniversalTensorSquare.sg35124`, `OAI.UniversalTensorSquare.sg35262`, `OAI.UniversalTensorSquare.sg35264`, `OAI.UniversalTensorSquare.sg35266`, `OAI.UniversalTensorSquare.sg35269`, `OAI.UniversalTensorSquare.sg35271`, `OAI.UniversalTensorSquare.sg35272`, `OAI.UniversalTensorSquare.sg35284`, `OAI.UniversalTensorSquare.sg9868`, `OAI.UniversalTensorSquare.sg9872` and `OAI.UniversalTensorSquare.sg9873` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1523)

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

lemma sg1523 : RowSquare [7,2,1,1] [3,3,3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
