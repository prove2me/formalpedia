-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg10867
-- name    : OAI.UniversalTensorSquare.sg10867
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:32:33.536012+00:00
-- url     : https://prove2.me/theorems/df13fd1e-01a2-44c4-b8b7-69e8beebbef9
-- title:
--   OAI.UniversalTensorSquare.sg10867: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg10867` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg10867 : RowSquare [7,6,2,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_307All`, `OAI.UniversalTensorSquare.degreeTree43_311All`, `OAI.UniversalTensorSquare.degreeTree43_315All`, `OAI.UniversalTensorSquare.degreeTree43_316All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_333All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_351All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_371All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_390All`, `OAI.UniversalTensorSquare.degreeTree43_428All`, `OAI.UniversalTensorSquare.degreeTree43_431All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_484All`, `OAI.UniversalTensorSquare.degreeTree43_492All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_497All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.degreeTree43_520All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_560All`, `OAI.UniversalTensorSquare.degreeTree43_646All`, `OAI.UniversalTensorSquare.sg18243`, `OAI.UniversalTensorSquare.sg18244`, `OAI.UniversalTensorSquare.sg18245`, `OAI.UniversalTensorSquare.sg18274`, `OAI.UniversalTensorSquare.sg26981`, `OAI.UniversalTensorSquare.sg27642`, `OAI.UniversalTensorSquare.sg27701`, `OAI.UniversalTensorSquare.sg27710`, `OAI.UniversalTensorSquare.sg27760`, `OAI.UniversalTensorSquare.sg27768`, `OAI.UniversalTensorSquare.sg27844`, `OAI.UniversalTensorSquare.sg27942`, `OAI.UniversalTensorSquare.sg27950`, `OAI.UniversalTensorSquare.sg27990`, `OAI.UniversalTensorSquare.sg27999`, `OAI.UniversalTensorSquare.sg28434`, `OAI.UniversalTensorSquare.sg28443`, `OAI.UniversalTensorSquare.sg28480`, `OAI.UniversalTensorSquare.sg28498`, `OAI.UniversalTensorSquare.sg28625`, `OAI.UniversalTensorSquare.sg29150`, `OAI.UniversalTensorSquare.sg29168`, `OAI.UniversalTensorSquare.sg29202`, `OAI.UniversalTensorSquare.sg29535`, `OAI.UniversalTensorSquare.sg29954`, `OAI.UniversalTensorSquare.sg30701`, `OAI.UniversalTensorSquare.sg30758`, `OAI.UniversalTensorSquare.sg31113`, `OAI.UniversalTensorSquare.sg31787`, `OAI.UniversalTensorSquare.sg31842`, `OAI.UniversalTensorSquare.sg31885` and `OAI.UniversalTensorSquare.sg31899` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg10867)

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

lemma sg10867 : RowSquare [7,6,2,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
