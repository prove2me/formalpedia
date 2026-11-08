-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_mul_bounds_g
-- name    : OAI.SharpPlanar.IntegerIntervals.mul_bounds_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T18:49:24.983121+00:00
-- url     : https://prove2.me/theorems/f6e5490a-7a96-4f45-bb5d-f7e2a3734364
-- title:
--   OAI.SharpPlanar.IntegerIntervals.mul_bounds_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.mul_bounds` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma mul_bounds_g {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
--       (mulLo a b:ℝ) ≤ (precision:ℝ)^2*(x*y) ∧
--         (precision:ℝ)^2*(x*y) ≤ (mulHi a b:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox`, `OAI.SharpPlanar.IntegerIntervals.mulHi`, `OAI.SharpPlanar.IntegerIntervals.mulLo` and `OAI.SharpPlanar.IntegerIntervals.precision` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.mul_contains_g` and `OAI.SharpPlanar.IntegerIntervals.RBox.mul_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.mul_bounds)

import Mathlib
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma mul_bounds_g {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (mulLo a b:ℝ) ≤ (precision:ℝ)^2*(x*y) ∧
      (precision:ℝ)^2*(x*y) ≤ (mulHi a b:ℝ) := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
