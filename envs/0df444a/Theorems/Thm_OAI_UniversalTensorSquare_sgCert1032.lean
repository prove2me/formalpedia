-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1032
-- name    : OAI.UniversalTensorSquare.sgCert1032
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:36.196421+00:00
-- url     : https://prove2.me/theorems/7c1a35cf-8ba6-4c69-9859-663f9b1b84d7
-- title:
--   OAI.UniversalTensorSquare.sgCert1032: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1032` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1032 : solveCompact 10 (.full [6,4]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
--       (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1032 sgT1032) sgFlag1032 = 16
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1032` and `OAI.UniversalTensorSquare.sgFlag1032` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1032` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_633All`, `OAI.UniversalTensorSquare.sg1032`, `OAI.UniversalTensorSquare.sg16697`, `OAI.UniversalTensorSquare.sg16804`, `OAI.UniversalTensorSquare.sg19327`, `OAI.UniversalTensorSquare.sg31972`, `OAI.UniversalTensorSquare.sg34479`, `OAI.UniversalTensorSquare.sg34556`, `OAI.UniversalTensorSquare.sg34579`, `OAI.UniversalTensorSquare.sg35446`, `OAI.UniversalTensorSquare.sg36122`, `OAI.UniversalTensorSquare.sg36124`, `OAI.UniversalTensorSquare.sg36126`, `OAI.UniversalTensorSquare.sg36147`, `OAI.UniversalTensorSquare.sg36174`, `OAI.UniversalTensorSquare.sg36176`, `OAI.UniversalTensorSquare.sg36178`, `OAI.UniversalTensorSquare.sg36512`, `OAI.UniversalTensorSquare.sg36515`, `OAI.UniversalTensorSquare.sg36517`, `OAI.UniversalTensorSquare.sg37176`, `OAI.UniversalTensorSquare.sg37402`, `OAI.UniversalTensorSquare.sg37443`, `OAI.UniversalTensorSquare.sg37546`, `OAI.UniversalTensorSquare.sg37561`, `OAI.UniversalTensorSquare.sg37608`, `OAI.UniversalTensorSquare.sg37609`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37644`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg37674`, `OAI.UniversalTensorSquare.sg37847`, `OAI.UniversalTensorSquare.sg37849`, `OAI.UniversalTensorSquare.sg37851`, `OAI.UniversalTensorSquare.sg37997`, `OAI.UniversalTensorSquare.sg37999`, `OAI.UniversalTensorSquare.sg38001`, `OAI.UniversalTensorSquare.sg38496`, `OAI.UniversalTensorSquare.sg38856`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg39004`, `OAI.UniversalTensorSquare.sg39006`, `OAI.UniversalTensorSquare.sg39420`, `OAI.UniversalTensorSquare.sg39441`, `OAI.UniversalTensorSquare.sg39444`, `OAI.UniversalTensorSquare.sg39887`, `OAI.UniversalTensorSquare.sg39890`, `OAI.UniversalTensorSquare.sg40009`, `OAI.UniversalTensorSquare.sg40011`, `OAI.UniversalTensorSquare.sg40012`, `OAI.UniversalTensorSquare.sg41447`, `OAI.UniversalTensorSquare.sg42059`, `OAI.UniversalTensorSquare.sg42068`, `OAI.UniversalTensorSquare.sg42319`, `OAI.UniversalTensorSquare.sg42320`, `OAI.UniversalTensorSquare.sg42326`, `OAI.UniversalTensorSquare.sg42767`, `OAI.UniversalTensorSquare.sg43153`, `OAI.UniversalTensorSquare.sg43229`, `OAI.UniversalTensorSquare.sg5438`, `OAI.UniversalTensorSquare.sg5859`, `OAI.UniversalTensorSquare.sg6640`, `OAI.UniversalTensorSquare.sg6641`, `OAI.UniversalTensorSquare.sg6676`, `OAI.UniversalTensorSquare.sg6681`, `OAI.UniversalTensorSquare.sg6683`, `OAI.UniversalTensorSquare.sg6688`, `OAI.UniversalTensorSquare.sg6787`, `OAI.UniversalTensorSquare.sg6822`, `OAI.UniversalTensorSquare.sg7187`, `OAI.UniversalTensorSquare.sg7349`, `OAI.UniversalTensorSquare.sg7356`, `OAI.UniversalTensorSquare.sg7358`, `OAI.UniversalTensorSquare.sg7388`, `OAI.UniversalTensorSquare.sg7901`, `OAI.UniversalTensorSquare.sg9093`, `OAI.UniversalTensorSquare.sg9108`, `OAI.UniversalTensorSquare.sg9254`, `OAI.UniversalTensorSquare.sg9259`, `OAI.UniversalTensorSquare.sg9349`, `OAI.UniversalTensorSquare.sg9358`, `OAI.UniversalTensorSquare.sg9554`, `OAI.UniversalTensorSquare.sg9618`, `OAI.UniversalTensorSquare.sg9802`, `OAI.UniversalTensorSquare.sg9831`, `OAI.UniversalTensorSquare.sg9840`, `OAI.UniversalTensorSquare.sg9842`, `OAI.UniversalTensorSquare.sg9906` and `OAI.UniversalTensorSquare.sg9932` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1032)

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

lemma sgCert1032 : solveCompact 10 (.full [6,4]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1032 sgT1032) sgFlag1032 = 16 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
