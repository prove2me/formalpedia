-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1001
-- name    : OAI.UniversalTensorSquare.sgCert1001
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:43.531199+00:00
-- url     : https://prove2.me/theorems/2732f146-bf9b-460a-ab4e-5f520b68b743
-- title:
--   OAI.UniversalTensorSquare.sgCert1001: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1001` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1001 : solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
--       (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1001 sgT1001) sgFlag1001 = 240
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1001` and `OAI.UniversalTensorSquare.sgFlag1001` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1001` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_740All`, `OAI.UniversalTensorSquare.sg1001`, `OAI.UniversalTensorSquare.sg16151`, `OAI.UniversalTensorSquare.sg17464`, `OAI.UniversalTensorSquare.sg18057`, `OAI.UniversalTensorSquare.sg18064`, `OAI.UniversalTensorSquare.sg20474`, `OAI.UniversalTensorSquare.sg27311`, `OAI.UniversalTensorSquare.sg29512`, `OAI.UniversalTensorSquare.sg33664`, `OAI.UniversalTensorSquare.sg34025`, `OAI.UniversalTensorSquare.sg34028`, `OAI.UniversalTensorSquare.sg34445`, `OAI.UniversalTensorSquare.sg34450`, `OAI.UniversalTensorSquare.sg34604`, `OAI.UniversalTensorSquare.sg34610`, `OAI.UniversalTensorSquare.sg35274`, `OAI.UniversalTensorSquare.sg35371`, `OAI.UniversalTensorSquare.sg35377`, `OAI.UniversalTensorSquare.sg35460`, `OAI.UniversalTensorSquare.sg35466`, `OAI.UniversalTensorSquare.sg36220`, `OAI.UniversalTensorSquare.sg37353`, `OAI.UniversalTensorSquare.sg37363`, `OAI.UniversalTensorSquare.sg37368`, `OAI.UniversalTensorSquare.sg37468`, `OAI.UniversalTensorSquare.sg37470`, `OAI.UniversalTensorSquare.sg37473`, `OAI.UniversalTensorSquare.sg37492`, `OAI.UniversalTensorSquare.sg37493`, `OAI.UniversalTensorSquare.sg37621`, `OAI.UniversalTensorSquare.sg37624`, `OAI.UniversalTensorSquare.sg37770`, `OAI.UniversalTensorSquare.sg38342`, `OAI.UniversalTensorSquare.sg38345`, `OAI.UniversalTensorSquare.sg38658`, `OAI.UniversalTensorSquare.sg38668`, `OAI.UniversalTensorSquare.sg38671`, `OAI.UniversalTensorSquare.sg38673`, `OAI.UniversalTensorSquare.sg40198`, `OAI.UniversalTensorSquare.sg40200`, `OAI.UniversalTensorSquare.sg40203`, `OAI.UniversalTensorSquare.sg40714`, `OAI.UniversalTensorSquare.sg40716`, `OAI.UniversalTensorSquare.sg40757`, `OAI.UniversalTensorSquare.sg40759`, `OAI.UniversalTensorSquare.sg41051`, `OAI.UniversalTensorSquare.sg41053`, `OAI.UniversalTensorSquare.sg41060`, `OAI.UniversalTensorSquare.sg41062`, `OAI.UniversalTensorSquare.sg41113`, `OAI.UniversalTensorSquare.sg41142`, `OAI.UniversalTensorSquare.sg41144`, `OAI.UniversalTensorSquare.sg41167`, `OAI.UniversalTensorSquare.sg41169`, `OAI.UniversalTensorSquare.sg41302`, `OAI.UniversalTensorSquare.sg41386`, `OAI.UniversalTensorSquare.sg41388`, `OAI.UniversalTensorSquare.sg41405`, `OAI.UniversalTensorSquare.sg41408`, `OAI.UniversalTensorSquare.sg41460`, `OAI.UniversalTensorSquare.sg41817`, `OAI.UniversalTensorSquare.sg41819`, `OAI.UniversalTensorSquare.sg42025`, `OAI.UniversalTensorSquare.sg42829`, `OAI.UniversalTensorSquare.sg42832`, `OAI.UniversalTensorSquare.sg42908`, `OAI.UniversalTensorSquare.sg42977`, `OAI.UniversalTensorSquare.sg42978`, `OAI.UniversalTensorSquare.sg43007`, `OAI.UniversalTensorSquare.sg43008`, `OAI.UniversalTensorSquare.sg43016`, `OAI.UniversalTensorSquare.sg43077`, `OAI.UniversalTensorSquare.sg43141`, `OAI.UniversalTensorSquare.sg4489`, `OAI.UniversalTensorSquare.sg4548`, `OAI.UniversalTensorSquare.sg5423`, `OAI.UniversalTensorSquare.sg6050`, `OAI.UniversalTensorSquare.sg6187`, `OAI.UniversalTensorSquare.sg6245`, `OAI.UniversalTensorSquare.sg6777`, `OAI.UniversalTensorSquare.sg6918`, `OAI.UniversalTensorSquare.sg7092`, `OAI.UniversalTensorSquare.sg7098`, `OAI.UniversalTensorSquare.sg7154`, `OAI.UniversalTensorSquare.sg7230`, `OAI.UniversalTensorSquare.sg7247`, `OAI.UniversalTensorSquare.sg7320`, `OAI.UniversalTensorSquare.sg7589`, `OAI.UniversalTensorSquare.sg7591`, `OAI.UniversalTensorSquare.sg7653`, `OAI.UniversalTensorSquare.sg7656`, `OAI.UniversalTensorSquare.sg7675`, `OAI.UniversalTensorSquare.sg7687`, `OAI.UniversalTensorSquare.sg7714`, `OAI.UniversalTensorSquare.sg8013`, `OAI.UniversalTensorSquare.sg8018`, `OAI.UniversalTensorSquare.sg8559`, `OAI.UniversalTensorSquare.sg8884`, `OAI.UniversalTensorSquare.sg9223`, `OAI.UniversalTensorSquare.sg9271`, `OAI.UniversalTensorSquare.sg9282`, `OAI.UniversalTensorSquare.sg9289`, `OAI.UniversalTensorSquare.sg9291`, `OAI.UniversalTensorSquare.sg9304`, `OAI.UniversalTensorSquare.sg9561`, `OAI.UniversalTensorSquare.sg9570`, `OAI.UniversalTensorSquare.sg9738`, `OAI.UniversalTensorSquare.sg9761`, `OAI.UniversalTensorSquare.sg9862` and `OAI.UniversalTensorSquare.sg9892` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1001)

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

lemma sgCert1001 : solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1001 sgT1001) sgFlag1001 = 240 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
