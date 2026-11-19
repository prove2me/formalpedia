-- Prove2me | Theorems.Thm_OAI_Saxl_dominates_transpose
-- name    : OAI.Saxl.dominates_transpose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:11.097228+00:00
-- url     : https://prove2.me/theorems/ef8ce84e-c65a-4046-9e1f-a34203b2db2c
-- title:
--   OAI.Saxl.dominates_transpose: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.dominates_transpose` of [lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
--       (h : Dominates μ ν) : Dominates ν.transpose μ.transpose
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Dominates` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.balance_dominance` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean (declaration OAI.Saxl.dominates_transpose)

import Mathlib
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

theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
    (h : Dominates μ ν) : Dominates ν.transpose μ.transpose := by
  sorry

open scoped MonoidAlgebra

end Saxl

end

end OAI
end
