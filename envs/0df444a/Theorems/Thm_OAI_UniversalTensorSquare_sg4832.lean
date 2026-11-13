-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4832
-- name    : OAI.UniversalTensorSquare.sg4832
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:17:43.948546+00:00
-- url     : https://prove2.me/theorems/f3d10217-24ed-4384-b410-34883dd8835a
-- title:
--   OAI.UniversalTensorSquare.sg4832: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4832` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4832 : RowSquare [5,5,3,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree41_4All`, `OAI.UniversalTensorSquare.degreeTree43_112All`, `OAI.UniversalTensorSquare.degreeTree43_215All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_244All`, `OAI.UniversalTensorSquare.degreeTree43_272All`, `OAI.UniversalTensorSquare.degreeTree43_275All`, `OAI.UniversalTensorSquare.degreeTree43_563All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.degreeTree43_93All`, `OAI.UniversalTensorSquare.sg14307`, `OAI.UniversalTensorSquare.sg14308`, `OAI.UniversalTensorSquare.sg23411`, `OAI.UniversalTensorSquare.sg23556`, `OAI.UniversalTensorSquare.sg23564`, `OAI.UniversalTensorSquare.sg24295`, `OAI.UniversalTensorSquare.sg24301`, `OAI.UniversalTensorSquare.sg24649`, `OAI.UniversalTensorSquare.sg24655`, `OAI.UniversalTensorSquare.sg24765`, `OAI.UniversalTensorSquare.sg24797`, `OAI.UniversalTensorSquare.sg24824`, `OAI.UniversalTensorSquare.sg24866`, `OAI.UniversalTensorSquare.sg25083`, `OAI.UniversalTensorSquare.sg25091`, `OAI.UniversalTensorSquare.sg25921`, `OAI.UniversalTensorSquare.sg25953`, `OAI.UniversalTensorSquare.sg26015`, `OAI.UniversalTensorSquare.sg26314`, `OAI.UniversalTensorSquare.sg26346`, `OAI.UniversalTensorSquare.sg26554`, `OAI.UniversalTensorSquare.sg26562`, `OAI.UniversalTensorSquare.sg26781`, `OAI.UniversalTensorSquare.sg27071`, `OAI.UniversalTensorSquare.sg27153`, `OAI.UniversalTensorSquare.sg27185`, `OAI.UniversalTensorSquare.sg27192`, `OAI.UniversalTensorSquare.sg27246`, `OAI.UniversalTensorSquare.sg27320`, `OAI.UniversalTensorSquare.sg27328`, `OAI.UniversalTensorSquare.sg27357`, `OAI.UniversalTensorSquare.sg28760`, `OAI.UniversalTensorSquare.sg28912`, `OAI.UniversalTensorSquare.sg29384`, `OAI.UniversalTensorSquare.sg29549`, `OAI.UniversalTensorSquare.sg29763`, `OAI.UniversalTensorSquare.sg29771`, `OAI.UniversalTensorSquare.sg30063`, `OAI.UniversalTensorSquare.sg30143`, `OAI.UniversalTensorSquare.sg30175`, `OAI.UniversalTensorSquare.sg30299`, `OAI.UniversalTensorSquare.sg30307`, `OAI.UniversalTensorSquare.sg30465`, `OAI.UniversalTensorSquare.sg30772`, `OAI.UniversalTensorSquare.sg30804`, `OAI.UniversalTensorSquare.sg30863`, `OAI.UniversalTensorSquare.sg30990`, `OAI.UniversalTensorSquare.sg31137`, `OAI.UniversalTensorSquare.sg31171`, `OAI.UniversalTensorSquare.sg31179` and `OAI.UniversalTensorSquare.sg31186` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg4832)

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

lemma sg4832 : RowSquare [5,5,3,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
