-- Prove2me | Theorems.Thm_OAI_Saxl_dominated_support_uts
-- name    : OAI.Saxl.dominated_support_uts
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:11:25.209564+00:00
-- url     : https://prove2.me/theorems/7e4f0929-6367-4595-9560-b27221d011b5
-- title:
--   OAI.Saxl.dominated_support_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.dominated_support` of [lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem dominated_support_uts (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
--       (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
--       ∃ f : Representation.IntertwiningMap (spechtRep t)
--         (staircaseCyclic m).toRepresentation, f ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.staircase` and `OAI.Saxl.staircaseCyclic` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Dominates` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.cyclic_saxl_conjecture` and `OAI.UniversalTensorSquare.candidateHighWord_support` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean (declaration OAI.Saxl.dominated_support)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

theorem dominated_support_uts (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, f ≠ 0 := by
  sorry

end Saxl

end

end OAI
end
