-- Prove2me | Theorems.Thm_OAI_SharpPlanar_directKernel_norm
-- name    : OAI.SharpPlanar.directKernel_norm
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T14:22:57.761196+00:00
-- url     : https://prove2.me/theorems/c11fd936-7b03-41a4-ac1e-a17b14842da9
-- title:
--   OAI.SharpPlanar.directKernel_norm: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.directKernel_norm` of [lean/OAI/Analysis/PlanarPacking/DirectBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/DirectBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open MeasureTheory Set IntegerBasis`, `open scoped BigOperators`):
--
--   ```lean
--   lemma directKernel_norm (ell : ℕ) (s t : ℝ) :
--       ‖directKernel ell s t‖=(Real.pi*|t|)^ell
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.directKernel` (definitions bundle `OAIQ098D002` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Pmoment_norm_bound` and `OAI.SharpPlanar.direct_piece_bound` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/DirectBounds.lean (declaration OAI.SharpPlanar.directKernel_norm)

import Mathlib
import Definitions.Def_OAIQ098D002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory Set IntegerBasis
open scoped BigOperators
lemma directKernel_norm (ell : ℕ) (s t : ℝ) :
    ‖directKernel ell s t‖=(Real.pi*|t|)^ell := by
  sorry
end SharpPlanar

end OAI
end
