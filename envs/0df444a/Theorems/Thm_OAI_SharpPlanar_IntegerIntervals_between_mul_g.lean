-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_between_mul_g
-- name    : OAI.SharpPlanar.IntegerIntervals.between_mul_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T16:16:43.601022+00:00
-- url     : https://prove2.me/theorems/e6a6c944-845f-4a62-8f68-d4c7e86f3113
-- title:
--   OAI.SharpPlanar.IntegerIntervals.between_mul_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.between_mul` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma between_mul_g {a b y x L U : ℝ} (hy : a ≤ y ∧ y ≤ b)
--       (ha : L ≤ x*a ∧ x*a ≤ U) (hb : L ≤ x*b ∧ x*b ≤ U) :
--       L ≤ x*y ∧ x*y ≤ U
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.RBox.scale_contains_g` and `OAI.SharpPlanar.IntegerIntervals.real_mul_bounds_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.between_mul)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma between_mul_g {a b y x L U : ℝ} (hy : a ≤ y ∧ y ≤ b)
    (ha : L ≤ x*a ∧ x*a ≤ U) (hb : L ≤ x*b ∧ x*b ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
