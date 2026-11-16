-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
-- name    : OAI.UniversalTensorSquare.eight_kronecker_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:38:57.708204+00:00
-- url     : https://prove2.me/theorems/b9b68131-a278-4412-8059-50a8af165b84
-- title:
--   OAI.UniversalTensorSquare.eight_kronecker_pos: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.eight_kronecker_pos` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   theorem eight_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 8) :
--       0 < kronecker (canonicalTableau eightWitness eightWitness_card)
--         (canonicalTableau eightWitness eightWitness_card) (canonicalTableau ν hν)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.eightWitness` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.eightWitness_card` (definitions bundle `OAIQ259US012` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.degreeTree62_37All`, `OAI.UniversalTensorSquare.degreeTree62_403All`, `OAI.UniversalTensorSquare.degreeTree62_487All`, `OAI.UniversalTensorSquare.degreeTree62_520All`, `OAI.UniversalTensorSquare.degreeTree62_546All`, `OAI.UniversalTensorSquare.degreeTree62_581All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_591All`, `OAI.UniversalTensorSquare.degreeTree62_607All`, `OAI.UniversalTensorSquare.degreeTree62_60All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_620All`, `OAI.UniversalTensorSquare.degreeTree62_661All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_673All`, `OAI.UniversalTensorSquare.degreeTree62_705All`, `OAI.UniversalTensorSquare.degreeTree62_799All`, `OAI.UniversalTensorSquare.degreeTree62_984All`, `OAI.UniversalTensorSquare.degreeTree62_993All`, `OAI.UniversalTensorSquare.degreeTree62_99All`, `OAI.UniversalTensorSquare.sg11241`, `OAI.UniversalTensorSquare.sg11948`, `OAI.UniversalTensorSquare.sg11983`, `OAI.UniversalTensorSquare.sg11997`, `OAI.UniversalTensorSquare.sg12031`, `OAI.UniversalTensorSquare.sg12034`, `OAI.UniversalTensorSquare.sg12043`, `OAI.UniversalTensorSquare.sg12152`, `OAI.UniversalTensorSquare.sg12520`, `OAI.UniversalTensorSquare.sg14557`, `OAI.UniversalTensorSquare.sg14607`, `OAI.UniversalTensorSquare.sg14616`, `OAI.UniversalTensorSquare.sg14631`, `OAI.UniversalTensorSquare.sg14647`, `OAI.UniversalTensorSquare.sg14664`, `OAI.UniversalTensorSquare.sg15710`, `OAI.UniversalTensorSquare.sg15944`, `OAI.UniversalTensorSquare.sg16476`, `OAI.UniversalTensorSquare.sg16652`, `OAI.UniversalTensorSquare.sg16654`, `OAI.UniversalTensorSquare.sg16668`, `OAI.UniversalTensorSquare.sg33017`, `OAI.UniversalTensorSquare.sg33124` and `OAI.UniversalTensorSquare.sg38540` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean (declaration OAI.UniversalTensorSquare.eight_kronecker_pos)

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

theorem eight_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 8) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau ν hν) := by
  sorry

universe u

end
end UniversalTensorSquare
end

end OAI
end
