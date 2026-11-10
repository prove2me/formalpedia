-- Prove2me | Theorems.Thm_OAI_SharpPlanar_piece_damping_bound_g
-- name    : OAI.SharpPlanar.piece_damping_bound_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:52:07.965745+00:00
-- url     : https://prove2.me/theorems/9e38a54d-dd7d-4a58-ba76-6396c02ed01c
-- title:
--   OAI.SharpPlanar.piece_damping_bound_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.piece_damping_bound` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma piece_damping_bound_g (j : Fin 6) {t : ℝ}
--       (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
--       dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.dampingCap` and `OAI.SharpPlanar.slopeCap` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.piece_kernel_bounds_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.piece_damping_bound)

import Mathlib
import Definitions.Def_OAIQ098G362

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma piece_damping_bound_g (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im := by
  sorry

end SharpPlanar

end OAI
end
