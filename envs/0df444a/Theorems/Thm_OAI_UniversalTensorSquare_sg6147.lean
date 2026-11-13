-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6147
-- name    : OAI.UniversalTensorSquare.sg6147
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:23:54.676219+00:00
-- url     : https://prove2.me/theorems/545e4f88-312f-4a62-bd08-bd5d39932d9b
-- title:
--   OAI.UniversalTensorSquare.sg6147: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6147` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6147 : RowSquare [5,4,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_102All`, `OAI.UniversalTensorSquare.degreeTree39_103All`, `OAI.UniversalTensorSquare.degreeTree39_106All`, `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree39_119All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_57All`, `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree39_73All`, `OAI.UniversalTensorSquare.degreeTree39_74All`, `OAI.UniversalTensorSquare.degreeTree39_80All`, `OAI.UniversalTensorSquare.degreeTree39_88All`, `OAI.UniversalTensorSquare.degreeTree39_95All`, `OAI.UniversalTensorSquare.sg21959`, `OAI.UniversalTensorSquare.sg22609`, `OAI.UniversalTensorSquare.sg22743`, `OAI.UniversalTensorSquare.sg22753`, `OAI.UniversalTensorSquare.sg22816`, `OAI.UniversalTensorSquare.sg22837`, `OAI.UniversalTensorSquare.sg22873`, `OAI.UniversalTensorSquare.sg22884`, `OAI.UniversalTensorSquare.sg22931`, `OAI.UniversalTensorSquare.sg22968`, `OAI.UniversalTensorSquare.sg22995`, `OAI.UniversalTensorSquare.sg23016`, `OAI.UniversalTensorSquare.sg23051`, `OAI.UniversalTensorSquare.sg23075`, `OAI.UniversalTensorSquare.sg23086`, `OAI.UniversalTensorSquare.sg23116`, `OAI.UniversalTensorSquare.sg23159`, `OAI.UniversalTensorSquare.sg23177`, `OAI.UniversalTensorSquare.sg23184`, `OAI.UniversalTensorSquare.sg23308`, `OAI.UniversalTensorSquare.sg23343`, `OAI.UniversalTensorSquare.sg23424`, `OAI.UniversalTensorSquare.sg23456` and `OAI.UniversalTensorSquare.sg23481` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean (declaration OAI.UniversalTensorSquare.sg6147)

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

lemma sg6147 : RowSquare [5,4,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
