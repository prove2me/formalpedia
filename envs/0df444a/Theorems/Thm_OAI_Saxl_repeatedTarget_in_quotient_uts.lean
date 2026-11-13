-- Prove2me | Theorems.Thm_OAI_Saxl_repeatedTarget_in_quotient_uts
-- name    : OAI.Saxl.repeatedTarget_in_quotient_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:10:31.488515+00:00
-- url     : https://prove2.me/theorems/4c4b8d58-84d1-46f6-a2be-f875397070da
-- title:
--   OAI.Saxl.repeatedTarget_in_quotient_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.repeatedTarget_in_quotient` of [lean/OAI/RepresentationTheory/Saxl/DominatedQuotient.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/DominatedQuotient.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem repeatedTarget_in_quotient_uts (m : ℕ)
--       (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
--       Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.stairRowTableau`, `OAI.Saxl.stairTableau`, `OAI.Saxl.staircase` and `OAI.Saxl.staircaseCyclic` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.dominatedQuotient`, `OAI.Saxl.repeatedTarget` and `OAI.Saxl.signTwist` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.WordSpace`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.dominated_support_uts` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/DominatedQuotient.lean (declaration OAI.Saxl.repeatedTarget_in_quotient)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

theorem repeatedTarget_in_quotient_uts (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range := by
  sorry

end Saxl

end

end OAI
end
