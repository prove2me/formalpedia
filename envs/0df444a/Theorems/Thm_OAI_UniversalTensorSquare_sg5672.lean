-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg5672
-- name    : OAI.UniversalTensorSquare.sg5672
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:22:06.544195+00:00
-- url     : https://prove2.me/theorems/00ea2edd-abb4-4744-8bc5-867aea68e2ac
-- title:
--   OAI.UniversalTensorSquare.sg5672: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg5672` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg5672 : RowSquare [6,5,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_51All`, `OAI.UniversalTensorSquare.degreeTree39_54All`, `OAI.UniversalTensorSquare.degreeTree39_55All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree39_73All`, `OAI.UniversalTensorSquare.degreeTree39_80All`, `OAI.UniversalTensorSquare.degreeTree39_83All`, `OAI.UniversalTensorSquare.degreeTree39_87All`, `OAI.UniversalTensorSquare.degreeTree39_89All`, `OAI.UniversalTensorSquare.degreeTree43_116All`, `OAI.UniversalTensorSquare.degreeTree43_207All`, `OAI.UniversalTensorSquare.degreeTree43_226All`, `OAI.UniversalTensorSquare.degreeTree43_248All`, `OAI.UniversalTensorSquare.degreeTree43_263All`, `OAI.UniversalTensorSquare.degreeTree43_267All`, `OAI.UniversalTensorSquare.degreeTree43_273All`, `OAI.UniversalTensorSquare.degreeTree43_285All`, `OAI.UniversalTensorSquare.degreeTree43_286All`, `OAI.UniversalTensorSquare.degreeTree43_290All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_348All`, `OAI.UniversalTensorSquare.degreeTree43_351All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_390All`, `OAI.UniversalTensorSquare.degreeTree43_409All`, `OAI.UniversalTensorSquare.degreeTree43_431All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.degreeTree43_501All`, `OAI.UniversalTensorSquare.degreeTree43_507All`, `OAI.UniversalTensorSquare.degreeTree43_553All`, `OAI.UniversalTensorSquare.degreeTree43_586All`, `OAI.UniversalTensorSquare.degreeTree43_587All`, `OAI.UniversalTensorSquare.degreeTree43_590All`, `OAI.UniversalTensorSquare.degreeTree43_84All`, `OAI.UniversalTensorSquare.degreeTree43_88All`, `OAI.UniversalTensorSquare.degreeTree43_93All`, `OAI.UniversalTensorSquare.sg10044`, `OAI.UniversalTensorSquare.sg14409`, `OAI.UniversalTensorSquare.sg14414`, `OAI.UniversalTensorSquare.sg15521`, `OAI.UniversalTensorSquare.sg15544`, `OAI.UniversalTensorSquare.sg22445`, `OAI.UniversalTensorSquare.sg22485`, `OAI.UniversalTensorSquare.sg22492`, `OAI.UniversalTensorSquare.sg22526`, `OAI.UniversalTensorSquare.sg22532`, `OAI.UniversalTensorSquare.sg22638`, `OAI.UniversalTensorSquare.sg22644`, `OAI.UniversalTensorSquare.sg22671`, `OAI.UniversalTensorSquare.sg22678`, `OAI.UniversalTensorSquare.sg22908`, `OAI.UniversalTensorSquare.sg22915`, `OAI.UniversalTensorSquare.sg22939`, `OAI.UniversalTensorSquare.sg23023`, `OAI.UniversalTensorSquare.sg23140`, `OAI.UniversalTensorSquare.sg23521`, `OAI.UniversalTensorSquare.sg23555`, `OAI.UniversalTensorSquare.sg23563`, `OAI.UniversalTensorSquare.sg23589`, `OAI.UniversalTensorSquare.sg23596`, `OAI.UniversalTensorSquare.sg24648`, `OAI.UniversalTensorSquare.sg24755`, `OAI.UniversalTensorSquare.sg24771`, `OAI.UniversalTensorSquare.sg24796`, `OAI.UniversalTensorSquare.sg24940`, `OAI.UniversalTensorSquare.sg25119`, `OAI.UniversalTensorSquare.sg25920`, `OAI.UniversalTensorSquare.sg25927`, `OAI.UniversalTensorSquare.sg25952`, `OAI.UniversalTensorSquare.sg26313`, `OAI.UniversalTensorSquare.sg26553`, `OAI.UniversalTensorSquare.sg26788`, `OAI.UniversalTensorSquare.sg26975`, `OAI.UniversalTensorSquare.sg27000`, `OAI.UniversalTensorSquare.sg27042`, `OAI.UniversalTensorSquare.sg27070`, `OAI.UniversalTensorSquare.sg27077`, `OAI.UniversalTensorSquare.sg27143`, `OAI.UniversalTensorSquare.sg27152`, `OAI.UniversalTensorSquare.sg27159`, `OAI.UniversalTensorSquare.sg27184`, `OAI.UniversalTensorSquare.sg27245`, `OAI.UniversalTensorSquare.sg27327`, `OAI.UniversalTensorSquare.sg27406`, `OAI.UniversalTensorSquare.sg28324`, `OAI.UniversalTensorSquare.sg28368`, `OAI.UniversalTensorSquare.sg28493`, `OAI.UniversalTensorSquare.sg28509`, `OAI.UniversalTensorSquare.sg28629`, `OAI.UniversalTensorSquare.sg28639`, `OAI.UniversalTensorSquare.sg28678`, `OAI.UniversalTensorSquare.sg28789`, `OAI.UniversalTensorSquare.sg28889`, `OAI.UniversalTensorSquare.sg29163`, `OAI.UniversalTensorSquare.sg29179`, `OAI.UniversalTensorSquare.sg29206`, `OAI.UniversalTensorSquare.sg29216`, `OAI.UniversalTensorSquare.sg29338`, `OAI.UniversalTensorSquare.sg29762`, `OAI.UniversalTensorSquare.sg29967`, `OAI.UniversalTensorSquare.sg29977`, `OAI.UniversalTensorSquare.sg29985`, `OAI.UniversalTensorSquare.sg30464`, `OAI.UniversalTensorSquare.sg30705`, `OAI.UniversalTensorSquare.sg30715`, `OAI.UniversalTensorSquare.sg30724`, `OAI.UniversalTensorSquare.sg30732`, `OAI.UniversalTensorSquare.sg30771`, `OAI.UniversalTensorSquare.sg30862`, `OAI.UniversalTensorSquare.sg31127`, `OAI.UniversalTensorSquare.sg31136`, `OAI.UniversalTensorSquare.sg31143`, `OAI.UniversalTensorSquare.sg31250` and `OAI.UniversalTensorSquare.sg8682` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg5672)

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

lemma sg5672 : RowSquare [6,5,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
