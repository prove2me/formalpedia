-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg315
-- name    : OAI.UniversalTensorSquare.sg315
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T00:36:50.227497+00:00
-- url     : https://prove2.me/theorems/f8316286-e19d-4523-9314-7bf5690a197d
-- title:
--   OAI.UniversalTensorSquare.sg315: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg315` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg315 : RowSquare [4,1,1,1,1] [2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_100All`, `OAI.UniversalTensorSquare.degreeTree41_11All`, `OAI.UniversalTensorSquare.degreeTree43_124All`, `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_192All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_253All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_306All`, `OAI.UniversalTensorSquare.degreeTree43_321All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree43_586All`, `OAI.UniversalTensorSquare.degreeTree43_59All`, `OAI.UniversalTensorSquare.degreeTree43_609All`, `OAI.UniversalTensorSquare.degreeTree43_615All`, `OAI.UniversalTensorSquare.degreeTree43_625All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree62_128All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_300All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_496All`, `OAI.UniversalTensorSquare.degreeTree62_597All`, `OAI.UniversalTensorSquare.degreeTree62_615All`, `OAI.UniversalTensorSquare.degreeTree62_673All`, `OAI.UniversalTensorSquare.degreeTree62_675All`, `OAI.UniversalTensorSquare.degreeTree62_854All`, `OAI.UniversalTensorSquare.sg14664`, `OAI.UniversalTensorSquare.sg22082`, `OAI.UniversalTensorSquare.sg22706`, `OAI.UniversalTensorSquare.sg23166`, `OAI.UniversalTensorSquare.sg23245`, `OAI.UniversalTensorSquare.sg23654`, `OAI.UniversalTensorSquare.sg24296`, `OAI.UniversalTensorSquare.sg24428`, `OAI.UniversalTensorSquare.sg24435`, `OAI.UniversalTensorSquare.sg24446`, `OAI.UniversalTensorSquare.sg24603`, `OAI.UniversalTensorSquare.sg24658`, `OAI.UniversalTensorSquare.sg24672`, `OAI.UniversalTensorSquare.sg24861`, `OAI.UniversalTensorSquare.sg24962`, `OAI.UniversalTensorSquare.sg25036`, `OAI.UniversalTensorSquare.sg25039`, `OAI.UniversalTensorSquare.sg25245`, `OAI.UniversalTensorSquare.sg25254`, `OAI.UniversalTensorSquare.sg25266`, `OAI.UniversalTensorSquare.sg25294`, `OAI.UniversalTensorSquare.sg25309`, `OAI.UniversalTensorSquare.sg25312`, `OAI.UniversalTensorSquare.sg25322`, `OAI.UniversalTensorSquare.sg25336`, `OAI.UniversalTensorSquare.sg25337`, `OAI.UniversalTensorSquare.sg25339`, `OAI.UniversalTensorSquare.sg25350`, `OAI.UniversalTensorSquare.sg25702`, `OAI.UniversalTensorSquare.sg26093`, `OAI.UniversalTensorSquare.sg26106`, `OAI.UniversalTensorSquare.sg26110`, `OAI.UniversalTensorSquare.sg26111`, `OAI.UniversalTensorSquare.sg26112`, `OAI.UniversalTensorSquare.sg26176`, `OAI.UniversalTensorSquare.sg26182`, `OAI.UniversalTensorSquare.sg26183`, `OAI.UniversalTensorSquare.sg26184`, `OAI.UniversalTensorSquare.sg26185`, `OAI.UniversalTensorSquare.sg26186`, `OAI.UniversalTensorSquare.sg26260`, `OAI.UniversalTensorSquare.sg26498`, `OAI.UniversalTensorSquare.sg26509`, `OAI.UniversalTensorSquare.sg26511`, `OAI.UniversalTensorSquare.sg26752`, `OAI.UniversalTensorSquare.sg26759`, `OAI.UniversalTensorSquare.sg26762`, `OAI.UniversalTensorSquare.sg26763`, `OAI.UniversalTensorSquare.sg26764`, `OAI.UniversalTensorSquare.sg26765`, `OAI.UniversalTensorSquare.sg26860`, `OAI.UniversalTensorSquare.sg26913`, `OAI.UniversalTensorSquare.sg26943`, `OAI.UniversalTensorSquare.sg26954`, `OAI.UniversalTensorSquare.sg26959`, `OAI.UniversalTensorSquare.sg26960`, `OAI.UniversalTensorSquare.sg27186`, `OAI.UniversalTensorSquare.sg27265`, `OAI.UniversalTensorSquare.sg27268`, `OAI.UniversalTensorSquare.sg27358`, `OAI.UniversalTensorSquare.sg27422`, `OAI.UniversalTensorSquare.sg27471`, `OAI.UniversalTensorSquare.sg27484`, `OAI.UniversalTensorSquare.sg27565`, `OAI.UniversalTensorSquare.sg27573`, `OAI.UniversalTensorSquare.sg27595`, `OAI.UniversalTensorSquare.sg27599`, `OAI.UniversalTensorSquare.sg27601`, `OAI.UniversalTensorSquare.sg27603`, `OAI.UniversalTensorSquare.sg28780`, `OAI.UniversalTensorSquare.sg28786`, `OAI.UniversalTensorSquare.sg29090`, `OAI.UniversalTensorSquare.sg29093`, `OAI.UniversalTensorSquare.sg29388`, `OAI.UniversalTensorSquare.sg29582`, `OAI.UniversalTensorSquare.sg29801`, `OAI.UniversalTensorSquare.sg29852`, `OAI.UniversalTensorSquare.sg29854`, `OAI.UniversalTensorSquare.sg29940`, `OAI.UniversalTensorSquare.sg29942`, `OAI.UniversalTensorSquare.sg29946`, `OAI.UniversalTensorSquare.sg29948`, `OAI.UniversalTensorSquare.sg30446`, `OAI.UniversalTensorSquare.sg30564`, `OAI.UniversalTensorSquare.sg32601`, `OAI.UniversalTensorSquare.sg602` and `OAI.UniversalTensorSquare.sg9215` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg315)

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

lemma sg315 : RowSquare [4,1,1,1,1] [2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
