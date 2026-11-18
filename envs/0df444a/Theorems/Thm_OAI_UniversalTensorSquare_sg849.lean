-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg849
-- name    : OAI.UniversalTensorSquare.sg849
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:41:26.310759+00:00
-- url     : https://prove2.me/theorems/196a9691-cf1f-49ad-a264-6ee7f89ef435
-- title:
--   OAI.UniversalTensorSquare.sg849: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg849` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg849 : RowSquare [4,3,2,1] [1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree20_6All`, `OAI.UniversalTensorSquare.degreeTree20_9All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree43_275All`, `OAI.UniversalTensorSquare.degreeTree43_291All`, `OAI.UniversalTensorSquare.degreeTree43_505All`, `OAI.UniversalTensorSquare.degreeTree43_589All`, `OAI.UniversalTensorSquare.sg10965`, `OAI.UniversalTensorSquare.sg11008`, `OAI.UniversalTensorSquare.sg11034`, `OAI.UniversalTensorSquare.sg11039`, `OAI.UniversalTensorSquare.sg13114`, `OAI.UniversalTensorSquare.sg13184`, `OAI.UniversalTensorSquare.sg13329`, `OAI.UniversalTensorSquare.sg13350`, `OAI.UniversalTensorSquare.sg13421`, `OAI.UniversalTensorSquare.sg13436`, `OAI.UniversalTensorSquare.sg20592`, `OAI.UniversalTensorSquare.sg21568`, `OAI.UniversalTensorSquare.sg21591`, `OAI.UniversalTensorSquare.sg21595`, `OAI.UniversalTensorSquare.sg22039`, `OAI.UniversalTensorSquare.sg23013`, `OAI.UniversalTensorSquare.sg23345`, `OAI.UniversalTensorSquare.sg23353`, `OAI.UniversalTensorSquare.sg23358`, `OAI.UniversalTensorSquare.sg23392`, `OAI.UniversalTensorSquare.sg23400`, `OAI.UniversalTensorSquare.sg23508`, `OAI.UniversalTensorSquare.sg23559`, `OAI.UniversalTensorSquare.sg23594`, `OAI.UniversalTensorSquare.sg25131`, `OAI.UniversalTensorSquare.sg26975`, `OAI.UniversalTensorSquare.sg27036`, `OAI.UniversalTensorSquare.sg27644`, `OAI.UniversalTensorSquare.sg27653`, `OAI.UniversalTensorSquare.sg27660`, `OAI.UniversalTensorSquare.sg27703`, `OAI.UniversalTensorSquare.sg28373`, `OAI.UniversalTensorSquare.sg28469`, `OAI.UniversalTensorSquare.sg28617`, `OAI.UniversalTensorSquare.sg28899`, `OAI.UniversalTensorSquare.sg29206`, `OAI.UniversalTensorSquare.sg29234`, `OAI.UniversalTensorSquare.sg29321`, `OAI.UniversalTensorSquare.sg29339`, `OAI.UniversalTensorSquare.sg29358`, `OAI.UniversalTensorSquare.sg29386`, `OAI.UniversalTensorSquare.sg29429`, `OAI.UniversalTensorSquare.sg29957`, `OAI.UniversalTensorSquare.sg29967`, `OAI.UniversalTensorSquare.sg29987`, `OAI.UniversalTensorSquare.sg30018`, `OAI.UniversalTensorSquare.sg30117`, `OAI.UniversalTensorSquare.sg30365`, `OAI.UniversalTensorSquare.sg30705`, `OAI.UniversalTensorSquare.sg30716`, `OAI.UniversalTensorSquare.sg30726`, `OAI.UniversalTensorSquare.sg30735`, `OAI.UniversalTensorSquare.sg30774`, `OAI.UniversalTensorSquare.sg31129`, `OAI.UniversalTensorSquare.sg31173`, `OAI.UniversalTensorSquare.sg34478`, `OAI.UniversalTensorSquare.sg34640`, `OAI.UniversalTensorSquare.sg35131`, `OAI.UniversalTensorSquare.sg35272`, `OAI.UniversalTensorSquare.sg35486`, `OAI.UniversalTensorSquare.sg35510`, `OAI.UniversalTensorSquare.sg35542`, `OAI.UniversalTensorSquare.sg36402`, `OAI.UniversalTensorSquare.sg36465`, `OAI.UniversalTensorSquare.sg37770`, `OAI.UniversalTensorSquare.sg4087`, `OAI.UniversalTensorSquare.sg4103`, `OAI.UniversalTensorSquare.sg5713`, `OAI.UniversalTensorSquare.sg6148`, `OAI.UniversalTensorSquare.sg8415`, `OAI.UniversalTensorSquare.sg8423`, `OAI.UniversalTensorSquare.sg8425`, `OAI.UniversalTensorSquare.sg8427`, `OAI.UniversalTensorSquare.sg8429`, `OAI.UniversalTensorSquare.sg8441` and `OAI.UniversalTensorSquare.sg8446` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg849)

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

lemma sg849 : RowSquare [4,3,2,1] [1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
