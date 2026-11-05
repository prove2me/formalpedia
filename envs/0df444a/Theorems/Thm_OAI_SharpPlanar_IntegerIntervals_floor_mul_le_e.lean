-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_floor_mul_le_e
-- name    : OAI.SharpPlanar.IntegerIntervals.floor_mul_le_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:41:28.648194+00:00
-- url     : https://prove2.me/theorems/05991420-2c1a-486e-a6b9-8315b1f09a0c
-- title:
--   OAI.SharpPlanar.IntegerIntervals.floor_mul_le_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.floor_mul_le` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma floor_mul_le_e (x : ℤ) {n : ℤ} (hn : 0 < n) : x/n*n ≤ x
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_e`, `OAI.SharpPlanar.IntegerIntervals.RBox.mul_check_e`, `OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_e`, `OAI.SharpPlanar.IntegerIntervals.RBox.scale_check_e` and `OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.floor_mul_le)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma floor_mul_le_e (x : ℤ) {n : ℤ} (hn : 0 < n) : x/n*n ≤ x := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
