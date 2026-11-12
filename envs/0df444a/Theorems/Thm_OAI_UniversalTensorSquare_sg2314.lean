-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2314
-- name    : OAI.UniversalTensorSquare.sg2314
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T23:31:59.020228+00:00
-- url     : https://prove2.me/theorems/e1add4a2-733a-48f4-a93f-561defa60782
-- title:
--   OAI.UniversalTensorSquare.sg2314: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2314` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2314 : RowSquare [7,3,2,1] [3,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_20All`, `OAI.UniversalTensorSquare.degreeTree58_1All`, `OAI.UniversalTensorSquare.degreeTree62_113All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_120All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_134All`, `OAI.UniversalTensorSquare.degreeTree62_136All`, `OAI.UniversalTensorSquare.degreeTree62_137All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_142All`, `OAI.UniversalTensorSquare.degreeTree62_375All`, `OAI.UniversalTensorSquare.degreeTree62_382All`, `OAI.UniversalTensorSquare.degreeTree62_384All`, `OAI.UniversalTensorSquare.degreeTree62_402All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_444All`, `OAI.UniversalTensorSquare.degreeTree62_449All`, `OAI.UniversalTensorSquare.degreeTree62_491All`, `OAI.UniversalTensorSquare.degreeTree62_502All`, `OAI.UniversalTensorSquare.degreeTree62_512All`, `OAI.UniversalTensorSquare.degreeTree62_534All`, `OAI.UniversalTensorSquare.degreeTree62_537All`, `OAI.UniversalTensorSquare.degreeTree62_538All`, `OAI.UniversalTensorSquare.degreeTree62_558All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_669All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_680All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_752All`, `OAI.UniversalTensorSquare.degreeTree62_758All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_771All`, `OAI.UniversalTensorSquare.degreeTree62_782All`, `OAI.UniversalTensorSquare.degreeTree62_78All`, `OAI.UniversalTensorSquare.degreeTree62_85All`, `OAI.UniversalTensorSquare.degreeTree62_87All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_925All`, `OAI.UniversalTensorSquare.degreeTree62_988All`, `OAI.UniversalTensorSquare.degreeTree62_98All`, `OAI.UniversalTensorSquare.sg16446`, `OAI.UniversalTensorSquare.sg18093`, `OAI.UniversalTensorSquare.sg18141`, `OAI.UniversalTensorSquare.sg18217`, `OAI.UniversalTensorSquare.sg21047`, `OAI.UniversalTensorSquare.sg21717`, `OAI.UniversalTensorSquare.sg21741`, `OAI.UniversalTensorSquare.sg21743`, `OAI.UniversalTensorSquare.sg22104`, `OAI.UniversalTensorSquare.sg22124`, `OAI.UniversalTensorSquare.sg22142`, `OAI.UniversalTensorSquare.sg22749`, `OAI.UniversalTensorSquare.sg22836`, `OAI.UniversalTensorSquare.sg23015`, `OAI.UniversalTensorSquare.sg23643`, `OAI.UniversalTensorSquare.sg23833`, `OAI.UniversalTensorSquare.sg23952`, `OAI.UniversalTensorSquare.sg24286`, `OAI.UniversalTensorSquare.sg25434`, `OAI.UniversalTensorSquare.sg25516`, `OAI.UniversalTensorSquare.sg25585`, `OAI.UniversalTensorSquare.sg25586`, `OAI.UniversalTensorSquare.sg25631`, `OAI.UniversalTensorSquare.sg25807`, `OAI.UniversalTensorSquare.sg26089`, `OAI.UniversalTensorSquare.sg31953`, `OAI.UniversalTensorSquare.sg32811`, `OAI.UniversalTensorSquare.sg33088`, `OAI.UniversalTensorSquare.sg33125`, `OAI.UniversalTensorSquare.sg33127`, `OAI.UniversalTensorSquare.sg33139`, `OAI.UniversalTensorSquare.sg33145`, `OAI.UniversalTensorSquare.sg33151`, `OAI.UniversalTensorSquare.sg33348`, `OAI.UniversalTensorSquare.sg33357`, `OAI.UniversalTensorSquare.sg33359`, `OAI.UniversalTensorSquare.sg33387`, `OAI.UniversalTensorSquare.sg33389`, `OAI.UniversalTensorSquare.sg33397`, `OAI.UniversalTensorSquare.sg33507`, `OAI.UniversalTensorSquare.sg33545`, `OAI.UniversalTensorSquare.sg33556`, `OAI.UniversalTensorSquare.sg33584`, `OAI.UniversalTensorSquare.sg35932`, `OAI.UniversalTensorSquare.sg35934`, `OAI.UniversalTensorSquare.sg35936`, `OAI.UniversalTensorSquare.sg36266`, `OAI.UniversalTensorSquare.sg36267`, `OAI.UniversalTensorSquare.sg36594`, `OAI.UniversalTensorSquare.sg36596`, `OAI.UniversalTensorSquare.sg36599`, `OAI.UniversalTensorSquare.sg36601`, `OAI.UniversalTensorSquare.sg37001`, `OAI.UniversalTensorSquare.sg37003`, `OAI.UniversalTensorSquare.sg37038`, `OAI.UniversalTensorSquare.sg37241`, `OAI.UniversalTensorSquare.sg37334`, `OAI.UniversalTensorSquare.sg37396`, `OAI.UniversalTensorSquare.sg37450`, `OAI.UniversalTensorSquare.sg37491`, `OAI.UniversalTensorSquare.sg37642`, `OAI.UniversalTensorSquare.sg37962`, `OAI.UniversalTensorSquare.sg37969`, `OAI.UniversalTensorSquare.sg38050`, `OAI.UniversalTensorSquare.sg38178`, `OAI.UniversalTensorSquare.sg38185`, `OAI.UniversalTensorSquare.sg38327`, `OAI.UniversalTensorSquare.sg38604`, `OAI.UniversalTensorSquare.sg38903`, `OAI.UniversalTensorSquare.sg38904`, `OAI.UniversalTensorSquare.sg39259`, `OAI.UniversalTensorSquare.sg39375`, `OAI.UniversalTensorSquare.sg39382`, `OAI.UniversalTensorSquare.sg40912`, `OAI.UniversalTensorSquare.sg40923`, `OAI.UniversalTensorSquare.sg40925`, `OAI.UniversalTensorSquare.sg40927`, `OAI.UniversalTensorSquare.sg40928`, `OAI.UniversalTensorSquare.sg41159`, `OAI.UniversalTensorSquare.sg41378`, `OAI.UniversalTensorSquare.sg41485`, `OAI.UniversalTensorSquare.sg41757`, `OAI.UniversalTensorSquare.sg41840`, `OAI.UniversalTensorSquare.sg41943`, `OAI.UniversalTensorSquare.sg42029`, `OAI.UniversalTensorSquare.sg42201`, `OAI.UniversalTensorSquare.sg42644`, `OAI.UniversalTensorSquare.sg42980` and `OAI.UniversalTensorSquare.sg43019` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2314)

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

lemma sg2314 : RowSquare [7,3,2,1] [3,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
