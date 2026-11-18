-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1000
-- name    : OAI.UniversalTensorSquare.sgCert1000
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:37.940121+00:00
-- url     : https://prove2.me/theorems/b565b655-5246-4c7e-9a37-9f9356827ac1
-- title:
--   OAI.UniversalTensorSquare.sgCert1000: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1000` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1000 : solveCompact 10 (.full [6,4]) (.full [6,1,1,1,1]) (.full [6,1,1,1,1])
--       (certificateEdges [6,1,1,1,1] [6,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1000 sgT1000) sgFlag1000 = 72
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1000` and `OAI.UniversalTensorSquare.sgFlag1000` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1000` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_374All`, `OAI.UniversalTensorSquare.sg1000`, `OAI.UniversalTensorSquare.sg16150`, `OAI.UniversalTensorSquare.sg16310`, `OAI.UniversalTensorSquare.sg24370`, `OAI.UniversalTensorSquare.sg33003`, `OAI.UniversalTensorSquare.sg33005`, `OAI.UniversalTensorSquare.sg34419`, `OAI.UniversalTensorSquare.sg34460`, `OAI.UniversalTensorSquare.sg34521`, `OAI.UniversalTensorSquare.sg34525`, `OAI.UniversalTensorSquare.sg35087`, `OAI.UniversalTensorSquare.sg35113`, `OAI.UniversalTensorSquare.sg35373`, `OAI.UniversalTensorSquare.sg35406`, `OAI.UniversalTensorSquare.sg35462`, `OAI.UniversalTensorSquare.sg36181`, `OAI.UniversalTensorSquare.sg36917`, `OAI.UniversalTensorSquare.sg36920`, `OAI.UniversalTensorSquare.sg37323`, `OAI.UniversalTensorSquare.sg37339`, `OAI.UniversalTensorSquare.sg37341`, `OAI.UniversalTensorSquare.sg37343`, `OAI.UniversalTensorSquare.sg37375`, `OAI.UniversalTensorSquare.sg37378`, `OAI.UniversalTensorSquare.sg37653`, `OAI.UniversalTensorSquare.sg37654`, `OAI.UniversalTensorSquare.sg37682`, `OAI.UniversalTensorSquare.sg37683`, `OAI.UniversalTensorSquare.sg38333`, `OAI.UniversalTensorSquare.sg38623`, `OAI.UniversalTensorSquare.sg38886`, `OAI.UniversalTensorSquare.sg39106`, `OAI.UniversalTensorSquare.sg39109`, `OAI.UniversalTensorSquare.sg40693`, `OAI.UniversalTensorSquare.sg40695`, `OAI.UniversalTensorSquare.sg41032`, `OAI.UniversalTensorSquare.sg41034`, `OAI.UniversalTensorSquare.sg41278`, `OAI.UniversalTensorSquare.sg41280`, `OAI.UniversalTensorSquare.sg41347`, `OAI.UniversalTensorSquare.sg41440`, `OAI.UniversalTensorSquare.sg41442`, `OAI.UniversalTensorSquare.sg42823`, `OAI.UniversalTensorSquare.sg42967`, `OAI.UniversalTensorSquare.sg42968`, `OAI.UniversalTensorSquare.sg42998`, `OAI.UniversalTensorSquare.sg42999`, `OAI.UniversalTensorSquare.sg43166`, `OAI.UniversalTensorSquare.sg4488`, `OAI.UniversalTensorSquare.sg4547`, `OAI.UniversalTensorSquare.sg4748`, `OAI.UniversalTensorSquare.sg5422`, `OAI.UniversalTensorSquare.sg5780`, `OAI.UniversalTensorSquare.sg6049`, `OAI.UniversalTensorSquare.sg6186`, `OAI.UniversalTensorSquare.sg6244`, `OAI.UniversalTensorSquare.sg6775`, `OAI.UniversalTensorSquare.sg6915`, `OAI.UniversalTensorSquare.sg6918`, `OAI.UniversalTensorSquare.sg6947`, `OAI.UniversalTensorSquare.sg7084`, `OAI.UniversalTensorSquare.sg7091`, `OAI.UniversalTensorSquare.sg7097`, `OAI.UniversalTensorSquare.sg7153`, `OAI.UniversalTensorSquare.sg7229`, `OAI.UniversalTensorSquare.sg7318`, `OAI.UniversalTensorSquare.sg7582`, `OAI.UniversalTensorSquare.sg7588`, `OAI.UniversalTensorSquare.sg7590`, `OAI.UniversalTensorSquare.sg7652`, `OAI.UniversalTensorSquare.sg7655`, `OAI.UniversalTensorSquare.sg7674`, `OAI.UniversalTensorSquare.sg7713`, `OAI.UniversalTensorSquare.sg8012`, `OAI.UniversalTensorSquare.sg8538`, `OAI.UniversalTensorSquare.sg9222`, `OAI.UniversalTensorSquare.sg9281`, `OAI.UniversalTensorSquare.sg9288`, `OAI.UniversalTensorSquare.sg9290`, `OAI.UniversalTensorSquare.sg9303`, `OAI.UniversalTensorSquare.sg9320`, `OAI.UniversalTensorSquare.sg9560`, `OAI.UniversalTensorSquare.sg9569` and `OAI.UniversalTensorSquare.sg9890` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1000)

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006

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

lemma sgCert1000 : solveCompact 10 (.full [6,4]) (.full [6,1,1,1,1]) (.full [6,1,1,1,1])
    (certificateEdges [6,1,1,1,1] [6,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1000 sgT1000) sgFlag1000 = 72 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
