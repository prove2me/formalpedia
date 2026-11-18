-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg71
-- name    : OAI.UniversalTensorSquare.sg71
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:12:49.710437+00:00
-- url     : https://prove2.me/theorems/bd9d9e81-9087-4c42-86cd-f4b317273e2f
-- title:
--   OAI.UniversalTensorSquare.sg71: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg71` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg71 : RowSquare [3,1,1,1] [3,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degreeTree41_9All`, `OAI.UniversalTensorSquare.degreeTree43_384All`, `OAI.UniversalTensorSquare.degreeTree43_508All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree62_727All`, `OAI.UniversalTensorSquare.degreeTreeAll41`, `OAI.UniversalTensorSquare.degreeTreeAll43`, `OAI.UniversalTensorSquare.sg21257`, `OAI.UniversalTensorSquare.sg21259`, `OAI.UniversalTensorSquare.sg21261`, `OAI.UniversalTensorSquare.sg21263`, `OAI.UniversalTensorSquare.sg22356`, `OAI.UniversalTensorSquare.sg23242`, `OAI.UniversalTensorSquare.sg23576`, `OAI.UniversalTensorSquare.sg23579`, `OAI.UniversalTensorSquare.sg26974`, `OAI.UniversalTensorSquare.sg26976`, `OAI.UniversalTensorSquare.sg26978`, `OAI.UniversalTensorSquare.sg26998`, `OAI.UniversalTensorSquare.sg27062`, `OAI.UniversalTensorSquare.sg27086`, `OAI.UniversalTensorSquare.sg27089`, `OAI.UniversalTensorSquare.sg27103`, `OAI.UniversalTensorSquare.sg27203`, `OAI.UniversalTensorSquare.sg27652`, `OAI.UniversalTensorSquare.sg27656`, `OAI.UniversalTensorSquare.sg27657`, `OAI.UniversalTensorSquare.sg27659`, `OAI.UniversalTensorSquare.sg27714`, `OAI.UniversalTensorSquare.sg27716`, `OAI.UniversalTensorSquare.sg27717`, `OAI.UniversalTensorSquare.sg27764`, `OAI.UniversalTensorSquare.sg27766`, `OAI.UniversalTensorSquare.sg27767`, `OAI.UniversalTensorSquare.sg27803`, `OAI.UniversalTensorSquare.sg27806`, `OAI.UniversalTensorSquare.sg27948`, `OAI.UniversalTensorSquare.sg27949`, `OAI.UniversalTensorSquare.sg28156`, `OAI.UniversalTensorSquare.sg28158`, `OAI.UniversalTensorSquare.sg29148`, `OAI.UniversalTensorSquare.sg29960`, `OAI.UniversalTensorSquare.sg30704`, `OAI.UniversalTensorSquare.sg30706`, `OAI.UniversalTensorSquare.sg30708`, `OAI.UniversalTensorSquare.sg30709`, `OAI.UniversalTensorSquare.sg30822`, `OAI.UniversalTensorSquare.sg31160`, `OAI.UniversalTensorSquare.sg31223`, `OAI.UniversalTensorSquare.sg31224`, `OAI.UniversalTensorSquare.sg31247`, `OAI.UniversalTensorSquare.sg31916`, `OAI.UniversalTensorSquare.sg31925`, `OAI.UniversalTensorSquare.sg35728`, `OAI.UniversalTensorSquare.sg35783`, `OAI.UniversalTensorSquare.sg35799`, `OAI.UniversalTensorSquare.sg35802`, `OAI.UniversalTensorSquare.sg35914`, `OAI.UniversalTensorSquare.sg35930`, `OAI.UniversalTensorSquare.sg35946`, `OAI.UniversalTensorSquare.sg35949`, `OAI.UniversalTensorSquare.sg35999`, `OAI.UniversalTensorSquare.sg36056`, `OAI.UniversalTensorSquare.sg36136`, `OAI.UniversalTensorSquare.sg36139`, `OAI.UniversalTensorSquare.sg36157`, `OAI.UniversalTensorSquare.sg36207`, `OAI.UniversalTensorSquare.sg36246`, `OAI.UniversalTensorSquare.sg36395`, `OAI.UniversalTensorSquare.sg36456`, `OAI.UniversalTensorSquare.sg36486`, `OAI.UniversalTensorSquare.sg36508`, `OAI.UniversalTensorSquare.sg36564`, `OAI.UniversalTensorSquare.sg36630`, `OAI.UniversalTensorSquare.sg36646`, `OAI.UniversalTensorSquare.sg36668`, `OAI.UniversalTensorSquare.sg36720`, `OAI.UniversalTensorSquare.sg36738`, `OAI.UniversalTensorSquare.sg36768`, `OAI.UniversalTensorSquare.sg36786`, `OAI.UniversalTensorSquare.sg36824`, `OAI.UniversalTensorSquare.sg36880`, `OAI.UniversalTensorSquare.sg36893`, `OAI.UniversalTensorSquare.sg36960`, `OAI.UniversalTensorSquare.sg37086`, `OAI.UniversalTensorSquare.sg37106`, `OAI.UniversalTensorSquare.sg37136`, `OAI.UniversalTensorSquare.sg37191`, `OAI.UniversalTensorSquare.sg37203`, `OAI.UniversalTensorSquare.sg37222`, `OAI.UniversalTensorSquare.sg37240`, `OAI.UniversalTensorSquare.sg37268`, `OAI.UniversalTensorSquare.sg37347`, `OAI.UniversalTensorSquare.sg37724`, `OAI.UniversalTensorSquare.sg37733`, `OAI.UniversalTensorSquare.sg37774`, `OAI.UniversalTensorSquare.sg38934`, `OAI.UniversalTensorSquare.sg38952`, `OAI.UniversalTensorSquare.sg38984`, `OAI.UniversalTensorSquare.sg38997`, `OAI.UniversalTensorSquare.sg39180`, `OAI.UniversalTensorSquare.sg39483`, `OAI.UniversalTensorSquare.sg39511`, `OAI.UniversalTensorSquare.sg39991`, `OAI.UniversalTensorSquare.sg39996`, `OAI.UniversalTensorSquare.sg40021`, `OAI.UniversalTensorSquare.sg40162`, `OAI.UniversalTensorSquare.sg40808`, `OAI.UniversalTensorSquare.sg41507`, `OAI.UniversalTensorSquare.sg41521`, `OAI.UniversalTensorSquare.sg41524`, `OAI.UniversalTensorSquare.sg41552`, `OAI.UniversalTensorSquare.sg42089`, `OAI.UniversalTensorSquare.sg42092`, `OAI.UniversalTensorSquare.sg42097`, `OAI.UniversalTensorSquare.sg42101`, `OAI.UniversalTensorSquare.sg42106`, `OAI.UniversalTensorSquare.sg42114`, `OAI.UniversalTensorSquare.sg42117`, `OAI.UniversalTensorSquare.sg42121`, `OAI.UniversalTensorSquare.sg42122`, `OAI.UniversalTensorSquare.sg42127`, `OAI.UniversalTensorSquare.sg42205`, `OAI.UniversalTensorSquare.sg42216`, `OAI.UniversalTensorSquare.sg42622`, `OAI.UniversalTensorSquare.sg42760`, `OAI.UniversalTensorSquare.sg42764`, `OAI.UniversalTensorSquare.sg43222`, `OAI.UniversalTensorSquare.sg7413`, `OAI.UniversalTensorSquare.sg8891` and `OAI.UniversalTensorSquare.sg8892` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sg71)

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

lemma sg71 : RowSquare [3,1,1,1] [3,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
