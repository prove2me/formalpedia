-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2137
-- name    : OAI.UniversalTensorSquare.sg2137
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T22:02:00.497208+00:00
-- url     : https://prove2.me/theorems/7cfd4bd0-caa4-4a7d-a304-f83f18e28d2d
-- title:
--   OAI.UniversalTensorSquare.sg2137: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2137` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2137 : RowSquare [5,3,3,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_104All`, `OAI.UniversalTensorSquare.degreeTree39_109All`, `OAI.UniversalTensorSquare.degreeTree39_114All`, `OAI.UniversalTensorSquare.degreeTree39_122All`, `OAI.UniversalTensorSquare.degreeTree43_314All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_382All`, `OAI.UniversalTensorSquare.degreeTree43_434All`, `OAI.UniversalTensorSquare.degreeTree62_302All`, `OAI.UniversalTensorSquare.degreeTree62_39All`, `OAI.UniversalTensorSquare.sg16147`, `OAI.UniversalTensorSquare.sg21462`, `OAI.UniversalTensorSquare.sg21467`, `OAI.UniversalTensorSquare.sg21470`, `OAI.UniversalTensorSquare.sg22772`, `OAI.UniversalTensorSquare.sg23028`, `OAI.UniversalTensorSquare.sg23263`, `OAI.UniversalTensorSquare.sg23268`, `OAI.UniversalTensorSquare.sg23285`, `OAI.UniversalTensorSquare.sg23318`, `OAI.UniversalTensorSquare.sg23401`, `OAI.UniversalTensorSquare.sg23509`, `OAI.UniversalTensorSquare.sg27977`, `OAI.UniversalTensorSquare.sg28176`, `OAI.UniversalTensorSquare.sg28211`, `OAI.UniversalTensorSquare.sg28514`, `OAI.UniversalTensorSquare.sg28652`, `OAI.UniversalTensorSquare.sg28683`, `OAI.UniversalTensorSquare.sg29184`, `OAI.UniversalTensorSquare.sg29260`, `OAI.UniversalTensorSquare.sg33803`, `OAI.UniversalTensorSquare.sg34460`, `OAI.UniversalTensorSquare.sg34659`, `OAI.UniversalTensorSquare.sg34720` and `OAI.UniversalTensorSquare.sg4735` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg2137)

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

lemma sg2137 : RowSquare [5,3,3,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
