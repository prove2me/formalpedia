-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg909
-- name    : OAI.UniversalTensorSquare.sg909
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:56:49.076173+00:00
-- url     : https://prove2.me/theorems/13f191a5-5395-4aa0-b009-b58ec6a2ce99
-- title:
--   OAI.UniversalTensorSquare.sg909: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg909` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg909 : RowSquare [5,1,1,1,1,1] [5,5]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_17All`, `OAI.UniversalTensorSquare.degreeTree43_120All`, `OAI.UniversalTensorSquare.degreeTree43_43All`, `OAI.UniversalTensorSquare.degreeTree43_485All`, `OAI.UniversalTensorSquare.degreeTree43_59All`, `OAI.UniversalTensorSquare.sg10221`, `OAI.UniversalTensorSquare.sg10226`, `OAI.UniversalTensorSquare.sg10230`, `OAI.UniversalTensorSquare.sg10274`, `OAI.UniversalTensorSquare.sg1332`, `OAI.UniversalTensorSquare.sg16237`, `OAI.UniversalTensorSquare.sg20882`, `OAI.UniversalTensorSquare.sg23640`, `OAI.UniversalTensorSquare.sg23975`, `OAI.UniversalTensorSquare.sg23977`, `OAI.UniversalTensorSquare.sg25905`, `OAI.UniversalTensorSquare.sg29996`, `OAI.UniversalTensorSquare.sg30736`, `OAI.UniversalTensorSquare.sg31243`, `OAI.UniversalTensorSquare.sg31601`, `OAI.UniversalTensorSquare.sg31777`, `OAI.UniversalTensorSquare.sg31971`, `OAI.UniversalTensorSquare.sg31981`, `OAI.UniversalTensorSquare.sg33657`, `OAI.UniversalTensorSquare.sg33659`, `OAI.UniversalTensorSquare.sg34018`, `OAI.UniversalTensorSquare.sg34512`, `OAI.UniversalTensorSquare.sg3540`, `OAI.UniversalTensorSquare.sg3545`, `OAI.UniversalTensorSquare.sg3589`, `OAI.UniversalTensorSquare.sg36071`, `OAI.UniversalTensorSquare.sg36076`, `OAI.UniversalTensorSquare.sg36157`, `OAI.UniversalTensorSquare.sg36232`, `OAI.UniversalTensorSquare.sg36235`, `OAI.UniversalTensorSquare.sg36237`, `OAI.UniversalTensorSquare.sg36246`, `OAI.UniversalTensorSquare.sg36300`, `OAI.UniversalTensorSquare.sg36303`, `OAI.UniversalTensorSquare.sg36305`, `OAI.UniversalTensorSquare.sg36579`, `OAI.UniversalTensorSquare.sg36584`, `OAI.UniversalTensorSquare.sg36993`, `OAI.UniversalTensorSquare.sg36995`, `OAI.UniversalTensorSquare.sg37057`, `OAI.UniversalTensorSquare.sg37483`, `OAI.UniversalTensorSquare.sg37941`, `OAI.UniversalTensorSquare.sg37944`, `OAI.UniversalTensorSquare.sg37946`, `OAI.UniversalTensorSquare.sg38316`, `OAI.UniversalTensorSquare.sg38355`, `OAI.UniversalTensorSquare.sg38528`, `OAI.UniversalTensorSquare.sg38531`, `OAI.UniversalTensorSquare.sg38688`, `OAI.UniversalTensorSquare.sg38727`, `OAI.UniversalTensorSquare.sg38849`, `OAI.UniversalTensorSquare.sg38920`, `OAI.UniversalTensorSquare.sg39144`, `OAI.UniversalTensorSquare.sg39147`, `OAI.UniversalTensorSquare.sg39164`, `OAI.UniversalTensorSquare.sg40631`, `OAI.UniversalTensorSquare.sg40633`, `OAI.UniversalTensorSquare.sg40924`, `OAI.UniversalTensorSquare.sg40926`, `OAI.UniversalTensorSquare.sg41155`, `OAI.UniversalTensorSquare.sg41808`, `OAI.UniversalTensorSquare.sg41826`, `OAI.UniversalTensorSquare.sg42173`, `OAI.UniversalTensorSquare.sg42174`, `OAI.UniversalTensorSquare.sg42235`, `OAI.UniversalTensorSquare.sg42236`, `OAI.UniversalTensorSquare.sg42663`, `OAI.UniversalTensorSquare.sg42701`, `OAI.UniversalTensorSquare.sg42838`, `OAI.UniversalTensorSquare.sg42839`, `OAI.UniversalTensorSquare.sg4842`, `OAI.UniversalTensorSquare.sg4890`, `OAI.UniversalTensorSquare.sg4949`, `OAI.UniversalTensorSquare.sg4960`, `OAI.UniversalTensorSquare.sg4984`, `OAI.UniversalTensorSquare.sg5629`, `OAI.UniversalTensorSquare.sg5630`, `OAI.UniversalTensorSquare.sg5631`, `OAI.UniversalTensorSquare.sg5763`, `OAI.UniversalTensorSquare.sg6505`, `OAI.UniversalTensorSquare.sg7328`, `OAI.UniversalTensorSquare.sg7362`, `OAI.UniversalTensorSquare.sg7373`, `OAI.UniversalTensorSquare.sg7563`, `OAI.UniversalTensorSquare.sg7606`, `OAI.UniversalTensorSquare.sg7711`, `OAI.UniversalTensorSquare.sg7712`, `OAI.UniversalTensorSquare.sg7713`, `OAI.UniversalTensorSquare.sg7714`, `OAI.UniversalTensorSquare.sg8429`, `OAI.UniversalTensorSquare.sg8559`, `OAI.UniversalTensorSquare.sg8626`, `OAI.UniversalTensorSquare.sg8665`, `OAI.UniversalTensorSquare.sg9492`, `OAI.UniversalTensorSquare.sg9493`, `OAI.UniversalTensorSquare.sg9507`, `OAI.UniversalTensorSquare.sg9518`, `OAI.UniversalTensorSquare.sg9527`, `OAI.UniversalTensorSquare.sg9538`, `OAI.UniversalTensorSquare.sg9551`, `OAI.UniversalTensorSquare.sg9562`, `OAI.UniversalTensorSquare.sg9590`, `OAI.UniversalTensorSquare.sg9605`, `OAI.UniversalTensorSquare.sg9648`, `OAI.UniversalTensorSquare.sg9722`, `OAI.UniversalTensorSquare.sg9727`, `OAI.UniversalTensorSquare.sg9748`, `OAI.UniversalTensorSquare.sg9778`, `OAI.UniversalTensorSquare.sg9794`, `OAI.UniversalTensorSquare.sg9824` and `OAI.UniversalTensorSquare.sg9995` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg909)

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

lemma sg909 : RowSquare [5,1,1,1,1,1] [5,5] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
