-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_trivial
-- name    : OAI.UniversalTensorSquare.rowSquare_trivial
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:23:11.428196+00:00
-- url     : https://prove2.me/theorems/990267d1-0266-4cce-b170-d4d3c1787c4d
-- title:
--   OAI.UniversalTensorSquare.rowSquare_trivial: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.rowSquare_trivial` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`, `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma rowSquare_trivial (p : List ℕ) (hn : 0 < p.sum) : RowSquare p [p.sum]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg0`, `OAI.UniversalTensorSquare.sg1`, `OAI.UniversalTensorSquare.sg103`, `OAI.UniversalTensorSquare.sg107`, `OAI.UniversalTensorSquare.sg108`, `OAI.UniversalTensorSquare.sg10867`, `OAI.UniversalTensorSquare.sg109`, `OAI.UniversalTensorSquare.sg113`, `OAI.UniversalTensorSquare.sg11531`, `OAI.UniversalTensorSquare.sg11532`, `OAI.UniversalTensorSquare.sg1177`, `OAI.UniversalTensorSquare.sg11874`, `OAI.UniversalTensorSquare.sg12`, `OAI.UniversalTensorSquare.sg122`, `OAI.UniversalTensorSquare.sg1232`, `OAI.UniversalTensorSquare.sg13`, `OAI.UniversalTensorSquare.sg1327`, `OAI.UniversalTensorSquare.sg15`, `OAI.UniversalTensorSquare.sg15004`, `OAI.UniversalTensorSquare.sg15293`, `OAI.UniversalTensorSquare.sg1650`, `OAI.UniversalTensorSquare.sg1682`, `OAI.UniversalTensorSquare.sg17146`, `OAI.UniversalTensorSquare.sg1754`, `OAI.UniversalTensorSquare.sg18274`, `OAI.UniversalTensorSquare.sg19`, `OAI.UniversalTensorSquare.sg2`, `OAI.UniversalTensorSquare.sg20`, `OAI.UniversalTensorSquare.sg2072`, `OAI.UniversalTensorSquare.sg21`, `OAI.UniversalTensorSquare.sg2105`, `OAI.UniversalTensorSquare.sg2107`, `OAI.UniversalTensorSquare.sg2137`, `OAI.UniversalTensorSquare.sg2138`, `OAI.UniversalTensorSquare.sg217`, `OAI.UniversalTensorSquare.sg22464`, `OAI.UniversalTensorSquare.sg2251`, `OAI.UniversalTensorSquare.sg226`, `OAI.UniversalTensorSquare.sg234`, `OAI.UniversalTensorSquare.sg235`, `OAI.UniversalTensorSquare.sg238`, `OAI.UniversalTensorSquare.sg248`, `OAI.UniversalTensorSquare.sg25`, `OAI.UniversalTensorSquare.sg2573`, `OAI.UniversalTensorSquare.sg2596`, `OAI.UniversalTensorSquare.sg2617`, `OAI.UniversalTensorSquare.sg2626`, `OAI.UniversalTensorSquare.sg2652`, `OAI.UniversalTensorSquare.sg269`, `OAI.UniversalTensorSquare.sg2702`, `OAI.UniversalTensorSquare.sg2758`, `OAI.UniversalTensorSquare.sg3`, `OAI.UniversalTensorSquare.sg306`, `OAI.UniversalTensorSquare.sg3065`, `OAI.UniversalTensorSquare.sg31934`, `OAI.UniversalTensorSquare.sg3239`, `OAI.UniversalTensorSquare.sg3521`, `OAI.UniversalTensorSquare.sg38`, `OAI.UniversalTensorSquare.sg3972`, `OAI.UniversalTensorSquare.sg3998`, `OAI.UniversalTensorSquare.sg4160`, `OAI.UniversalTensorSquare.sg421`, `OAI.UniversalTensorSquare.sg426`, `OAI.UniversalTensorSquare.sg427`, `OAI.UniversalTensorSquare.sg4345`, `OAI.UniversalTensorSquare.sg44`, `OAI.UniversalTensorSquare.sg445`, `OAI.UniversalTensorSquare.sg454`, `OAI.UniversalTensorSquare.sg4720`, `OAI.UniversalTensorSquare.sg4721`, `OAI.UniversalTensorSquare.sg4722`, `OAI.UniversalTensorSquare.sg474`, `OAI.UniversalTensorSquare.sg48`, `OAI.UniversalTensorSquare.sg4804`, `OAI.UniversalTensorSquare.sg4832`, `OAI.UniversalTensorSquare.sg49`, `OAI.UniversalTensorSquare.sg4930`, `OAI.UniversalTensorSquare.sg50`, `OAI.UniversalTensorSquare.sg509`, `OAI.UniversalTensorSquare.sg516`, `OAI.UniversalTensorSquare.sg54`, `OAI.UniversalTensorSquare.sg5672`, `OAI.UniversalTensorSquare.sg5735`, `OAI.UniversalTensorSquare.sg5736`, `OAI.UniversalTensorSquare.sg5757`, `OAI.UniversalTensorSquare.sg586`, `OAI.UniversalTensorSquare.sg6`, `OAI.UniversalTensorSquare.sg61`, `OAI.UniversalTensorSquare.sg6339`, `OAI.UniversalTensorSquare.sg6369`, `OAI.UniversalTensorSquare.sg6389`, `OAI.UniversalTensorSquare.sg6457`, `OAI.UniversalTensorSquare.sg6458`, `OAI.UniversalTensorSquare.sg65`, `OAI.UniversalTensorSquare.sg6502`, `OAI.UniversalTensorSquare.sg7`, `OAI.UniversalTensorSquare.sg718`, `OAI.UniversalTensorSquare.sg720`, `OAI.UniversalTensorSquare.sg730`, `OAI.UniversalTensorSquare.sg7454`, `OAI.UniversalTensorSquare.sg7483`, `OAI.UniversalTensorSquare.sg7812`, `OAI.UniversalTensorSquare.sg789`, `OAI.UniversalTensorSquare.sg7998`, `OAI.UniversalTensorSquare.sg8`, `OAI.UniversalTensorSquare.sg8468`, `OAI.UniversalTensorSquare.sg86`, `OAI.UniversalTensorSquare.sg8780`, `OAI.UniversalTensorSquare.sg8781`, `OAI.UniversalTensorSquare.sg8782`, `OAI.UniversalTensorSquare.sg8783`, `OAI.UniversalTensorSquare.sg910`, `OAI.UniversalTensorSquare.sg9594`, `OAI.UniversalTensorSquare.sg96`, `OAI.UniversalTensorSquare.smallSupports11` and `OAI.UniversalTensorSquare.smallSupports13` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean (declaration OAI.UniversalTensorSquare.rowSquare_trivial)

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
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_trivial (p : List ℕ) (hn : 0 < p.sum) : RowSquare p [p.sum] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
