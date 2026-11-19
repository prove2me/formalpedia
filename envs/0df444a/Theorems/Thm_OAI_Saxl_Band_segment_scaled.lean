-- Prove2me | Theorems.Thm_OAI_Saxl_Band_segment_scaled
-- name    : OAI.Saxl.Band.segment_scaled
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:21.296733+00:00
-- url     : https://prove2.me/theorems/73961fac-579e-4494-8542-bcc068074d02
-- title:
--   OAI.Saxl.Band.segment_scaled: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Band.segment_scaled` of [lean/OAI/RepresentationTheory/Saxl/BandMatrices.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/BandMatrices.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Band`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Band.ScaledBasis` and `OAI.Saxl.Band.segment` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proof of `OAI.Saxl.Band.blocks_scaled` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/BandMatrices.lean (declaration OAI.Saxl.Band.segment_scaled)

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

universe uA

namespace Saxl.Band

lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
  sorry

end Saxl.Band

end

end OAI
end
