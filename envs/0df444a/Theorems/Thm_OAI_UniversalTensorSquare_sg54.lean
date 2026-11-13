-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg54
-- name    : OAI.UniversalTensorSquare.sg54
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:20:51.493118+00:00
-- url     : https://prove2.me/theorems/25646273-41aa-44a2-a6b1-8bde8cc68fef
-- title:
--   OAI.UniversalTensorSquare.sg54: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg54` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg54 : RowSquare [2,1,1,1,1] [6]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree20_9All`, `OAI.UniversalTensorSquare.degreeTree35_14All`, `OAI.UniversalTensorSquare.degreeTree35_16All`, `OAI.UniversalTensorSquare.degreeTree39_103All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_57All`, `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree39_80All`, `OAI.UniversalTensorSquare.degreeTree39_88All`, `OAI.UniversalTensorSquare.degreeTree39_93All`, `OAI.UniversalTensorSquare.degreeTree39_94All`, `OAI.UniversalTensorSquare.degreeTree39_99All`, `OAI.UniversalTensorSquare.degreeTree43_133All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.degreeTree43_335All`, `OAI.UniversalTensorSquare.sg21522`, `OAI.UniversalTensorSquare.sg22596`, `OAI.UniversalTensorSquare.sg22610`, `OAI.UniversalTensorSquare.sg22661`, `OAI.UniversalTensorSquare.sg22721`, `OAI.UniversalTensorSquare.sg22725`, `OAI.UniversalTensorSquare.sg22736`, `OAI.UniversalTensorSquare.sg22744`, `OAI.UniversalTensorSquare.sg22754`, `OAI.UniversalTensorSquare.sg22790`, `OAI.UniversalTensorSquare.sg22809`, `OAI.UniversalTensorSquare.sg22817`, `OAI.UniversalTensorSquare.sg22840`, `OAI.UniversalTensorSquare.sg22850`, `OAI.UniversalTensorSquare.sg22863`, `OAI.UniversalTensorSquare.sg22932`, `OAI.UniversalTensorSquare.sg22965`, `OAI.UniversalTensorSquare.sg22969`, `OAI.UniversalTensorSquare.sg22988`, `OAI.UniversalTensorSquare.sg22996`, `OAI.UniversalTensorSquare.sg23019`, `OAI.UniversalTensorSquare.sg23044`, `OAI.UniversalTensorSquare.sg23052`, `OAI.UniversalTensorSquare.sg23063`, `OAI.UniversalTensorSquare.sg23089`, `OAI.UniversalTensorSquare.sg23092`, `OAI.UniversalTensorSquare.sg23112`, `OAI.UniversalTensorSquare.sg23120`, `OAI.UniversalTensorSquare.sg23147`, `OAI.UniversalTensorSquare.sg23160`, `OAI.UniversalTensorSquare.sg23180`, `OAI.UniversalTensorSquare.sg23188`, `OAI.UniversalTensorSquare.sg23206`, `OAI.UniversalTensorSquare.sg23228`, `OAI.UniversalTensorSquare.sg23270`, `OAI.UniversalTensorSquare.sg23274`, `OAI.UniversalTensorSquare.sg23301`, `OAI.UniversalTensorSquare.sg23309`, `OAI.UniversalTensorSquare.sg23320`, `OAI.UniversalTensorSquare.sg23333`, `OAI.UniversalTensorSquare.sg23346`, `OAI.UniversalTensorSquare.sg23349`, `OAI.UniversalTensorSquare.sg23417`, `OAI.UniversalTensorSquare.sg23425`, `OAI.UniversalTensorSquare.sg23444`, `OAI.UniversalTensorSquare.sg23457`, `OAI.UniversalTensorSquare.sg23477`, `OAI.UniversalTensorSquare.sg23485`, `OAI.UniversalTensorSquare.sg23704`, `OAI.UniversalTensorSquare.sg23713`, `OAI.UniversalTensorSquare.sg23734`, `OAI.UniversalTensorSquare.sg23741`, `OAI.UniversalTensorSquare.sg23746`, `OAI.UniversalTensorSquare.sg23749`, `OAI.UniversalTensorSquare.sg23770`, `OAI.UniversalTensorSquare.sg23781`, `OAI.UniversalTensorSquare.sg23810`, `OAI.UniversalTensorSquare.sg23821`, `OAI.UniversalTensorSquare.sg23824`, `OAI.UniversalTensorSquare.sg23848`, `OAI.UniversalTensorSquare.sg23852`, `OAI.UniversalTensorSquare.sg23862`, `OAI.UniversalTensorSquare.sg23866`, `OAI.UniversalTensorSquare.sg23912`, `OAI.UniversalTensorSquare.sg23916`, `OAI.UniversalTensorSquare.sg24043`, `OAI.UniversalTensorSquare.sg24053`, `OAI.UniversalTensorSquare.sg24074`, `OAI.UniversalTensorSquare.sg24084`, `OAI.UniversalTensorSquare.sg24094`, `OAI.UniversalTensorSquare.sg24100`, `OAI.UniversalTensorSquare.sg24145`, `OAI.UniversalTensorSquare.sg24151`, `OAI.UniversalTensorSquare.sg24515`, `OAI.UniversalTensorSquare.sg24553`, `OAI.UniversalTensorSquare.sg24583`, `OAI.UniversalTensorSquare.sg24591`, `OAI.UniversalTensorSquare.sg24604`, `OAI.UniversalTensorSquare.sg24608`, `OAI.UniversalTensorSquare.sg24969`, `OAI.UniversalTensorSquare.sg25043`, `OAI.UniversalTensorSquare.sg25371`, `OAI.UniversalTensorSquare.sg25422`, `OAI.UniversalTensorSquare.sg25507`, `OAI.UniversalTensorSquare.sg25526`, `OAI.UniversalTensorSquare.sg25530`, `OAI.UniversalTensorSquare.sg25546`, `OAI.UniversalTensorSquare.sg25592`, `OAI.UniversalTensorSquare.sg25648`, `OAI.UniversalTensorSquare.sg25660`, `OAI.UniversalTensorSquare.sg25746`, `OAI.UniversalTensorSquare.sg25750`, `OAI.UniversalTensorSquare.sg25756`, `OAI.UniversalTensorSquare.sg25772`, `OAI.UniversalTensorSquare.sg25836`, `OAI.UniversalTensorSquare.sg25994`, `OAI.UniversalTensorSquare.sg26035`, `OAI.UniversalTensorSquare.sg26049`, `OAI.UniversalTensorSquare.sg26070`, `OAI.UniversalTensorSquare.sg26108`, `OAI.UniversalTensorSquare.sg26119`, `OAI.UniversalTensorSquare.sg26372`, `OAI.UniversalTensorSquare.sg26629`, `OAI.UniversalTensorSquare.sg26663`, `OAI.UniversalTensorSquare.sg26675`, `OAI.UniversalTensorSquare.sg26690`, `OAI.UniversalTensorSquare.sg26716`, `OAI.UniversalTensorSquare.sg26725`, `OAI.UniversalTensorSquare.sg26756`, `OAI.UniversalTensorSquare.sg27105`, `OAI.UniversalTensorSquare.sg27114`, `OAI.UniversalTensorSquare.sg27181`, `OAI.UniversalTensorSquare.sg27274`, `OAI.UniversalTensorSquare.sg27378`, `OAI.UniversalTensorSquare.sg27516`, `OAI.UniversalTensorSquare.sg28906`, `OAI.UniversalTensorSquare.sg28939`, `OAI.UniversalTensorSquare.sg29576`, `OAI.UniversalTensorSquare.sg29607`, `OAI.UniversalTensorSquare.sg29820`, `OAI.UniversalTensorSquare.sg29833`, `OAI.UniversalTensorSquare.sg29863`, `OAI.UniversalTensorSquare.sg30333`, `OAI.UniversalTensorSquare.sg30493`, `OAI.UniversalTensorSquare.sg30514`, `OAI.UniversalTensorSquare.sg30518`, `OAI.UniversalTensorSquare.sg30524`, `OAI.UniversalTensorSquare.sg30529`, `OAI.UniversalTensorSquare.sg30545`, `OAI.UniversalTensorSquare.sg30550`, `OAI.UniversalTensorSquare.sg30569`, `OAI.UniversalTensorSquare.sg31106`, `OAI.UniversalTensorSquare.sg40067`, `OAI.UniversalTensorSquare.sg42652`, `OAI.UniversalTensorSquare.sg6157`, `OAI.UniversalTensorSquare.sg7912`, `OAI.UniversalTensorSquare.sg8477` and `OAI.UniversalTensorSquare.sg8494` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg54)

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

lemma sg54 : RowSquare [2,1,1,1,1] [6] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
