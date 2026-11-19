-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg15608
-- name    : OAI.UniversalTensorSquare.sg15608
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:07:22.907423+00:00
-- url     : https://prove2.me/theorems/fb01145b-c866-45f4-92ee-2c55c0178cb3
-- title:
--   OAI.UniversalTensorSquare.sg15608: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg15608` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes37.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes37.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg15608 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_537All`, `OAI.UniversalTensorSquare.degreeTree62_652All`, `OAI.UniversalTensorSquare.degreeTree62_656All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_809All`, `OAI.UniversalTensorSquare.degreeTree62_872All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.degreeTree62_959All`, `OAI.UniversalTensorSquare.degreeTree62_974All`, `OAI.UniversalTensorSquare.sg33115`, `OAI.UniversalTensorSquare.sg33163`, `OAI.UniversalTensorSquare.sg33818`, `OAI.UniversalTensorSquare.sg34485`, `OAI.UniversalTensorSquare.sg35390`, `OAI.UniversalTensorSquare.sg36294`, `OAI.UniversalTensorSquare.sg36928`, `OAI.UniversalTensorSquare.sg36957`, `OAI.UniversalTensorSquare.sg36974`, `OAI.UniversalTensorSquare.sg37031`, `OAI.UniversalTensorSquare.sg37042`, `OAI.UniversalTensorSquare.sg37370`, `OAI.UniversalTensorSquare.sg37400`, `OAI.UniversalTensorSquare.sg37441`, `OAI.UniversalTensorSquare.sg37484`, `OAI.UniversalTensorSquare.sg37543`, `OAI.UniversalTensorSquare.sg37559`, `OAI.UniversalTensorSquare.sg37588`, `OAI.UniversalTensorSquare.sg37635`, `OAI.UniversalTensorSquare.sg37669`, `OAI.UniversalTensorSquare.sg38130`, `OAI.UniversalTensorSquare.sg38156`, `OAI.UniversalTensorSquare.sg38172`, `OAI.UniversalTensorSquare.sg38184`, `OAI.UniversalTensorSquare.sg38252`, `OAI.UniversalTensorSquare.sg38267`, `OAI.UniversalTensorSquare.sg38279`, `OAI.UniversalTensorSquare.sg38308`, `OAI.UniversalTensorSquare.sg38317`, `OAI.UniversalTensorSquare.sg38356`, `OAI.UniversalTensorSquare.sg38524`, `OAI.UniversalTensorSquare.sg38538`, `OAI.UniversalTensorSquare.sg38550`, `OAI.UniversalTensorSquare.sg38651`, `OAI.UniversalTensorSquare.sg38686`, `OAI.UniversalTensorSquare.sg38749`, `OAI.UniversalTensorSquare.sg38786`, `OAI.UniversalTensorSquare.sg38808`, `OAI.UniversalTensorSquare.sg38817`, `OAI.UniversalTensorSquare.sg39153`, `OAI.UniversalTensorSquare.sg39321`, `OAI.UniversalTensorSquare.sg39332`, `OAI.UniversalTensorSquare.sg39366`, `OAI.UniversalTensorSquare.sg39413`, `OAI.UniversalTensorSquare.sg39457`, `OAI.UniversalTensorSquare.sg39487`, `OAI.UniversalTensorSquare.sg39515`, `OAI.UniversalTensorSquare.sg39600`, `OAI.UniversalTensorSquare.sg39623`, `OAI.UniversalTensorSquare.sg39656`, `OAI.UniversalTensorSquare.sg39838`, `OAI.UniversalTensorSquare.sg39895`, `OAI.UniversalTensorSquare.sg39913`, `OAI.UniversalTensorSquare.sg40181`, `OAI.UniversalTensorSquare.sg40514`, `OAI.UniversalTensorSquare.sg40638`, `OAI.UniversalTensorSquare.sg40700`, `OAI.UniversalTensorSquare.sg40719`, `OAI.UniversalTensorSquare.sg40730`, `OAI.UniversalTensorSquare.sg40738`, `OAI.UniversalTensorSquare.sg40770`, `OAI.UniversalTensorSquare.sg40940`, `OAI.UniversalTensorSquare.sg41056`, `OAI.UniversalTensorSquare.sg41067`, `OAI.UniversalTensorSquare.sg41073`, `OAI.UniversalTensorSquare.sg41114`, `OAI.UniversalTensorSquare.sg41124`, `OAI.UniversalTensorSquare.sg41130`, `OAI.UniversalTensorSquare.sg41149`, `OAI.UniversalTensorSquare.sg41154`, `OAI.UniversalTensorSquare.sg41176`, `OAI.UniversalTensorSquare.sg41240`, `OAI.UniversalTensorSquare.sg41275`, `OAI.UniversalTensorSquare.sg41344`, `OAI.UniversalTensorSquare.sg41375`, `OAI.UniversalTensorSquare.sg41394`, `OAI.UniversalTensorSquare.sg41409`, `OAI.UniversalTensorSquare.sg41430`, `OAI.UniversalTensorSquare.sg41451`, `OAI.UniversalTensorSquare.sg41466`, `OAI.UniversalTensorSquare.sg41480`, `OAI.UniversalTensorSquare.sg41628`, `OAI.UniversalTensorSquare.sg41636`, `OAI.UniversalTensorSquare.sg41641`, `OAI.UniversalTensorSquare.sg41721`, `OAI.UniversalTensorSquare.sg41728`, `OAI.UniversalTensorSquare.sg41733`, `OAI.UniversalTensorSquare.sg41749`, `OAI.UniversalTensorSquare.sg41753`, `OAI.UniversalTensorSquare.sg41781`, `OAI.UniversalTensorSquare.sg41807`, `OAI.UniversalTensorSquare.sg41823`, `OAI.UniversalTensorSquare.sg41836`, `OAI.UniversalTensorSquare.sg41881`, `OAI.UniversalTensorSquare.sg41893`, `OAI.UniversalTensorSquare.sg41914`, `OAI.UniversalTensorSquare.sg41921`, `OAI.UniversalTensorSquare.sg41935`, `OAI.UniversalTensorSquare.sg41939`, `OAI.UniversalTensorSquare.sg41955`, `OAI.UniversalTensorSquare.sg41990`, `OAI.UniversalTensorSquare.sg42003`, `OAI.UniversalTensorSquare.sg42015`, `OAI.UniversalTensorSquare.sg42056`, `OAI.UniversalTensorSquare.sg42066`, `OAI.UniversalTensorSquare.sg42170`, `OAI.UniversalTensorSquare.sg42194`, `OAI.UniversalTensorSquare.sg42197`, `OAI.UniversalTensorSquare.sg42232`, `OAI.UniversalTensorSquare.sg42242`, `OAI.UniversalTensorSquare.sg42260`, `OAI.UniversalTensorSquare.sg42281`, `OAI.UniversalTensorSquare.sg42295`, `OAI.UniversalTensorSquare.sg42311`, `OAI.UniversalTensorSquare.sg42336`, `OAI.UniversalTensorSquare.sg42347`, `OAI.UniversalTensorSquare.sg42383`, `OAI.UniversalTensorSquare.sg42389`, `OAI.UniversalTensorSquare.sg42404`, `OAI.UniversalTensorSquare.sg42417`, `OAI.UniversalTensorSquare.sg42431`, `OAI.UniversalTensorSquare.sg42453`, `OAI.UniversalTensorSquare.sg42490`, `OAI.UniversalTensorSquare.sg42522`, `OAI.UniversalTensorSquare.sg42528`, `OAI.UniversalTensorSquare.sg42583`, `OAI.UniversalTensorSquare.sg42606`, `OAI.UniversalTensorSquare.sg42621`, `OAI.UniversalTensorSquare.sg42637`, `OAI.UniversalTensorSquare.sg42651`, `OAI.UniversalTensorSquare.sg42673`, `OAI.UniversalTensorSquare.sg42690`, `OAI.UniversalTensorSquare.sg42742`, `OAI.UniversalTensorSquare.sg42786`, `OAI.UniversalTensorSquare.sg42797`, `OAI.UniversalTensorSquare.sg42808`, `OAI.UniversalTensorSquare.sg42811`, `OAI.UniversalTensorSquare.sg42820`, `OAI.UniversalTensorSquare.sg42826`, `OAI.UniversalTensorSquare.sg42842`, `OAI.UniversalTensorSquare.sg42848`, `OAI.UniversalTensorSquare.sg42865`, `OAI.UniversalTensorSquare.sg42876`, `OAI.UniversalTensorSquare.sg42884`, `OAI.UniversalTensorSquare.sg42890`, `OAI.UniversalTensorSquare.sg42897`, `OAI.UniversalTensorSquare.sg42902`, `OAI.UniversalTensorSquare.sg42904`, `OAI.UniversalTensorSquare.sg42913`, `OAI.UniversalTensorSquare.sg42915`, `OAI.UniversalTensorSquare.sg42920`, `OAI.UniversalTensorSquare.sg42933`, `OAI.UniversalTensorSquare.sg42945`, `OAI.UniversalTensorSquare.sg42955`, `OAI.UniversalTensorSquare.sg42963`, `OAI.UniversalTensorSquare.sg42970`, `OAI.UniversalTensorSquare.sg42975` and `OAI.UniversalTensorSquare.sg42991` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes37.lean (declaration OAI.UniversalTensorSquare.sg15608)

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

lemma sg15608 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
