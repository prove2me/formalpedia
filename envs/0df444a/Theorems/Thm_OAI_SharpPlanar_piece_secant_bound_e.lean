-- Prove2me | Theorems.Thm_OAI_SharpPlanar_piece_secant_bound_e
-- name    : OAI.SharpPlanar.piece_secant_bound_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T20:17:59.034652+00:00
-- url     : https://prove2.me/theorems/d45797ed-91be-414a-98bc-adc15e6c94e7
-- title:
--   OAI.SharpPlanar.piece_secant_bound_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.piece_secant_bound` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`):
--
--   ```lean
--   lemma piece_secant_bound_e (j : Fin 6) {t : ℝ}
--       (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
--       slopeCap j*(t^2+h^2)*((((j.val:ℝ)+1)/6)^2+h^2) ≤
--         h*B*(t+((j.val:ℝ)+1)/6)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.B` and `OAI.SharpPlanar.h` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.slopeCap` (definitions bundle `OAIQ098E125` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.piece_damping_bound_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.piece_secant_bound)

import Mathlib
import Definitions.Def_OAIQ098E125

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma piece_secant_bound_e (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    slopeCap j*(t^2+h^2)*((((j.val:ℝ)+1)/6)^2+h^2) ≤
      h*B*(t+((j.val:ℝ)+1)/6) := by
  sorry

end SharpPlanar

end OAI
end
