-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_eight_positive6
-- name    : OAI.UniversalTensorSquare.eight_positive6
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:48:19.939526+00:00
-- url     : https://prove2.me/theorems/6ad8058c-35e5-4642-a8ae-ac08fe54f6ed
-- title:
--   OAI.UniversalTensorSquare.eight_positive6: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.eight_positive6` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   lemma eight_positive6 :
--       0 < kronecker (canonicalTableau eightWitness eightWitness_card)
--         (canonicalTableau eightWitness eightWitness_card)
--         (canonicalTableau (diagramOfCols [4,1,1,1,1] (by decide))
--           (by exact diagramOfCols_card _ _ (by simp)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.diagramOfCols` and `OAI.UniversalTensorSquare.eightWitness` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.diagramOfCols_card` and `OAI.UniversalTensorSquare.eightWitness_card` (definitions bundle `OAIQ259US012` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_14All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree41_9All` and `OAI.UniversalTensorSquare.degreeTree43_112All` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean (declaration OAI.UniversalTensorSquare.eight_positive6)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

lemma eight_positive6 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [4,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  sorry

universe u

end
end UniversalTensorSquare
end

end OAI
end
