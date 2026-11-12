-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg21
-- name    : OAI.UniversalTensorSquare.sg21
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:57:33.900092+00:00
-- url     : https://prove2.me/theorems/fc253862-0651-4bbd-a4ae-7fa91a48e350
-- title:
--   OAI.UniversalTensorSquare.sg21: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg21` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg21 : RowSquare [1,1,1,1,1] [5]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_23All`, `OAI.UniversalTensorSquare.degreeTree39_17All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_57All`, `OAI.UniversalTensorSquare.degreeTree43_12All`, `OAI.UniversalTensorSquare.degreeTree43_133All`, `OAI.UniversalTensorSquare.degreeTree43_136All`, `OAI.UniversalTensorSquare.degreeTree43_137All`, `OAI.UniversalTensorSquare.degreeTree43_154All`, `OAI.UniversalTensorSquare.degreeTree43_15All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.degreeTree43_3All`, `OAI.UniversalTensorSquare.degreeTree43_432All`, `OAI.UniversalTensorSquare.degreeTree43_497All`, `OAI.UniversalTensorSquare.degreeTree43_503All`, `OAI.UniversalTensorSquare.degreeTree43_83All`, `OAI.UniversalTensorSquare.degreeTree43_9All`, `OAI.UniversalTensorSquare.degreeTree62_339All`, `OAI.UniversalTensorSquare.degreeTree62_340All`, `OAI.UniversalTensorSquare.degreeTree62_357All`, `OAI.UniversalTensorSquare.degreeTree62_397All`, `OAI.UniversalTensorSquare.degreeTree62_524All`, `OAI.UniversalTensorSquare.degreeTree62_629All`, `OAI.UniversalTensorSquare.degreeTree62_749All`, `OAI.UniversalTensorSquare.degreeTree62_755All`, `OAI.UniversalTensorSquare.degreeTree62_802All`, `OAI.UniversalTensorSquare.degreeTree62_981All`, `OAI.UniversalTensorSquare.degreeTree62_982All`, `OAI.UniversalTensorSquare.degreeTree62_999All`, `OAI.UniversalTensorSquare.degree_pos14`, `OAI.UniversalTensorSquare.sg10922`, `OAI.UniversalTensorSquare.sg10928`, `OAI.UniversalTensorSquare.sg10940`, `OAI.UniversalTensorSquare.sg10990`, `OAI.UniversalTensorSquare.sg10997`, `OAI.UniversalTensorSquare.sg11028`, `OAI.UniversalTensorSquare.sg11934`, `OAI.UniversalTensorSquare.sg11964`, `OAI.UniversalTensorSquare.sg12012`, `OAI.UniversalTensorSquare.sg12094`, `OAI.UniversalTensorSquare.sg12108`, `OAI.UniversalTensorSquare.sg12124`, `OAI.UniversalTensorSquare.sg12130`, `OAI.UniversalTensorSquare.sg12158`, `OAI.UniversalTensorSquare.sg12207`, `OAI.UniversalTensorSquare.sg12220`, `OAI.UniversalTensorSquare.sg12226`, `OAI.UniversalTensorSquare.sg12243`, `OAI.UniversalTensorSquare.sg12280`, `OAI.UniversalTensorSquare.sg12285`, `OAI.UniversalTensorSquare.sg12292`, `OAI.UniversalTensorSquare.sg12311`, `OAI.UniversalTensorSquare.sg12316`, `OAI.UniversalTensorSquare.sg12329`, `OAI.UniversalTensorSquare.sg13045`, `OAI.UniversalTensorSquare.sg13055`, `OAI.UniversalTensorSquare.sg13079`, `OAI.UniversalTensorSquare.sg13090`, `OAI.UniversalTensorSquare.sg13095`, `OAI.UniversalTensorSquare.sg13102`, `OAI.UniversalTensorSquare.sg13134`, `OAI.UniversalTensorSquare.sg13148`, `OAI.UniversalTensorSquare.sg13254`, `OAI.UniversalTensorSquare.sg13264`, `OAI.UniversalTensorSquare.sg13269`, `OAI.UniversalTensorSquare.sg13287`, `OAI.UniversalTensorSquare.sg13292`, `OAI.UniversalTensorSquare.sg13299`, `OAI.UniversalTensorSquare.sg13316`, `OAI.UniversalTensorSquare.sg13322`, `OAI.UniversalTensorSquare.sg13379`, `OAI.UniversalTensorSquare.sg13393`, `OAI.UniversalTensorSquare.sg13397`, `OAI.UniversalTensorSquare.sg13402`, `OAI.UniversalTensorSquare.sg13410`, `OAI.UniversalTensorSquare.sg13415`, `OAI.UniversalTensorSquare.sg13425`, `OAI.UniversalTensorSquare.sg13453`, `OAI.UniversalTensorSquare.sg13456`, `OAI.UniversalTensorSquare.sg13460`, `OAI.UniversalTensorSquare.sg13464`, `OAI.UniversalTensorSquare.sg13470`, `OAI.UniversalTensorSquare.sg13484`, `OAI.UniversalTensorSquare.sg14215`, `OAI.UniversalTensorSquare.sg18973`, `OAI.UniversalTensorSquare.sg19904`, `OAI.UniversalTensorSquare.sg21996`, `OAI.UniversalTensorSquare.sg22338`, `OAI.UniversalTensorSquare.sg22508`, `OAI.UniversalTensorSquare.sg22657`, `OAI.UniversalTensorSquare.sg22660`, `OAI.UniversalTensorSquare.sg22699`, `OAI.UniversalTensorSquare.sg22936`, `OAI.UniversalTensorSquare.sg23748`, `OAI.UniversalTensorSquare.sg23819`, `OAI.UniversalTensorSquare.sg24019`, `OAI.UniversalTensorSquare.sg24036`, `OAI.UniversalTensorSquare.sg24049`, `OAI.UniversalTensorSquare.sg24054`, `OAI.UniversalTensorSquare.sg24055`, `OAI.UniversalTensorSquare.sg24128`, `OAI.UniversalTensorSquare.sg24233`, `OAI.UniversalTensorSquare.sg24249`, `OAI.UniversalTensorSquare.sg24841`, `OAI.UniversalTensorSquare.sg24883`, `OAI.UniversalTensorSquare.sg25421`, `OAI.UniversalTensorSquare.sg25456`, `OAI.UniversalTensorSquare.sg25675`, `OAI.UniversalTensorSquare.sg25698`, `OAI.UniversalTensorSquare.sg25706`, `OAI.UniversalTensorSquare.sg26229`, `OAI.UniversalTensorSquare.sg26266`, `OAI.UniversalTensorSquare.sg26291`, `OAI.UniversalTensorSquare.sg26382`, `OAI.UniversalTensorSquare.sg26423`, `OAI.UniversalTensorSquare.sg26588`, `OAI.UniversalTensorSquare.sg27014`, `OAI.UniversalTensorSquare.sg27061`, `OAI.UniversalTensorSquare.sg27504`, `OAI.UniversalTensorSquare.sg29196`, `OAI.UniversalTensorSquare.sg29245`, `OAI.UniversalTensorSquare.sg29247`, `OAI.UniversalTensorSquare.sg29436`, `OAI.UniversalTensorSquare.sg30005`, `OAI.UniversalTensorSquare.sg30008`, `OAI.UniversalTensorSquare.sg30053`, `OAI.UniversalTensorSquare.sg30109`, `OAI.UniversalTensorSquare.sg30751`, `OAI.UniversalTensorSquare.sg30847`, `OAI.UniversalTensorSquare.sg31013`, `OAI.UniversalTensorSquare.sg35555`, `OAI.UniversalTensorSquare.sg35707`, `OAI.UniversalTensorSquare.sg35716`, `OAI.UniversalTensorSquare.sg35718`, `OAI.UniversalTensorSquare.sg35771`, `OAI.UniversalTensorSquare.sg35902`, `OAI.UniversalTensorSquare.sg35904`, `OAI.UniversalTensorSquare.sg35908`, `OAI.UniversalTensorSquare.sg35914`, `OAI.UniversalTensorSquare.sg35979`, `OAI.UniversalTensorSquare.sg36367`, `OAI.UniversalTensorSquare.sg36369`, `OAI.UniversalTensorSquare.sg36404`, `OAI.UniversalTensorSquare.sg36412`, `OAI.UniversalTensorSquare.sg36414`, `OAI.UniversalTensorSquare.sg36428`, `OAI.UniversalTensorSquare.sg36633`, `OAI.UniversalTensorSquare.sg36649`, `OAI.UniversalTensorSquare.sg37721`, `OAI.UniversalTensorSquare.sg37723`, `OAI.UniversalTensorSquare.sg37727`, `OAI.UniversalTensorSquare.sg37777`, `OAI.UniversalTensorSquare.sg37979`, `OAI.UniversalTensorSquare.sg38012`, `OAI.UniversalTensorSquare.sg38102`, `OAI.UniversalTensorSquare.sg39028`, `OAI.UniversalTensorSquare.sg39235`, `OAI.UniversalTensorSquare.sg40400`, `OAI.UniversalTensorSquare.sg40402`, `OAI.UniversalTensorSquare.sg40403`, `OAI.UniversalTensorSquare.sg40786`, `OAI.UniversalTensorSquare.sg40788`, `OAI.UniversalTensorSquare.sg40789`, `OAI.UniversalTensorSquare.sg40829`, `OAI.UniversalTensorSquare.sg40946`, `OAI.UniversalTensorSquare.sg41514`, `OAI.UniversalTensorSquare.sg41541`, `OAI.UniversalTensorSquare.sg43083`, `OAI.UniversalTensorSquare.sg6458`, `OAI.UniversalTensorSquare.sg7869`, `OAI.UniversalTensorSquare.sg7936` and `OAI.UniversalTensorSquare.sg7991` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg21)

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

lemma sg21 : RowSquare [1,1,1,1,1] [5] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
