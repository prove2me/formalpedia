-- Prove2me | Theorems.Thm_OAI_Saxl_twoBand_support_uts
-- name    : OAI.Saxl.twoBand_support_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:51:31.571879+00:00
-- url     : https://prove2.me/theorems/0290e948-5614-43b8-8d21-8dfb750e2771
-- title:
--   OAI.Saxl.twoBand_support_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.twoBand_support` of [lean/OAI/RepresentationTheory/Saxl/BandSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/BandSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem twoBand_support_uts (h : ℕ) (hh : 1 ≤ h) (μ : YoungDiagram)
--       (t : Tableau (bandSize h 2) μ) (hμ : μ.colLen 0 ≤ 4) :
--       ∃ f : Representation.IntertwiningMap (spechtRep t)
--         (cyclic (wordRep _ _) (stairBandWord h 2)).toRepresentation, f ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.staircase` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.bandSize` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.stairBandWord` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.cyclic_saxl_conjecture` and `OAI.UniversalTensorSquare.candidateHighWord_support` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/BandSupport.lean (declaration OAI.Saxl.twoBand_support)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

theorem twoBand_support_uts (h : ℕ) (hh : 1 ≤ h) (μ : YoungDiagram)
    (t : Tableau (bandSize h 2) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (stairBandWord h 2)).toRepresentation, f ≠ 0 := by
  sorry

end Saxl

end

end OAI
end
