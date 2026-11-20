-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_exceptional_pos77
-- name    : OAI.UniversalTensorSquare.exceptional_pos77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T14:03:10.405313+00:00
-- url     : https://prove2.me/theorems/1093e67c-b99a-430b-b459-92121f506e67
-- title:
--   OAI.UniversalTensorSquare.exceptional_pos77: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.exceptional_pos77` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance`):
--
--   ```lean
--   lemma exceptional_pos77 (μ : YoungDiagram) (hμ : μ.card = 77) :
--       0 < kronecker (canonicalTableau (candidate 10 5 1) exceptionalCard77)
--         (canonicalTableau (candidate 10 5 1) exceptionalCard77) (canonicalTableau μ hμ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.exceptionalCard77` (definitions bundle `OAIQ259US022` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_partition_exceptional` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean (declaration OAI.UniversalTensorSquare.exceptional_pos77)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma exceptional_pos77 (μ : YoungDiagram) (hμ : μ.card = 77) :
    0 < kronecker (canonicalTableau (candidate 10 5 1) exceptionalCard77)
      (canonicalTableau (candidate 10 5 1) exceptionalCard77) (canonicalTableau μ hμ) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
