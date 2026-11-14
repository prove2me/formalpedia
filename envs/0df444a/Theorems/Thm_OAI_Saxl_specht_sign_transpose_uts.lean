-- Prove2me | Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts
-- name    : OAI.Saxl.specht_sign_transpose_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:15:07.48013+00:00
-- url     : https://prove2.me/theorems/31d61031-8330-4a19-943d-f11b55616090
-- title:
--   OAI.Saxl.specht_sign_transpose_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.specht_sign_transpose` of [lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem specht_sign_transpose_uts {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
--       Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.signTwist` and `OAI.Saxl.transposeTableau` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.rowSquare_of_cols`, `OAI.UniversalTensorSquare.sg10937`, `OAI.UniversalTensorSquare.sg10938`, `OAI.UniversalTensorSquare.sg10939`, `OAI.UniversalTensorSquare.sg10943` and `OAI.UniversalTensorSquare.sg10944` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean (declaration OAI.Saxl.specht_sign_transpose)

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

universe uV

namespace Saxl

theorem specht_sign_transpose_uts {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  sorry
end Saxl

end

end OAI
end
