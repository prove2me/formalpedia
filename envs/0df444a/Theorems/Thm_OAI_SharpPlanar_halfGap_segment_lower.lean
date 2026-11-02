-- Prove2me | Theorems.Thm_OAI_SharpPlanar_halfGap_segment_lower
-- name    : OAI.SharpPlanar.halfGap_segment_lower
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T14:21:21.522536+00:00
-- url     : https://prove2.me/theorems/1fb227dc-c369-4017-89b8-1939d0690c11
-- title:
--   OAI.SharpPlanar.halfGap_segment_lower: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.halfGap_segment_lower` of [lean/OAI/Analysis/PlanarPacking/HalfGapAnalytic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HalfGapAnalytic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma halfGap_segment_lower {v m y s N : ℝ} (hv : v  ∈  Set.Icc 0 1)
--       (hm : N ≤ m) (hy : N ≤ m+y) (hs : s ∈ Set.uIcc m (m+y*v)) : N ≤ s
--   ```
--
--   **Used by.** The proofs of `OAI.SharpPlanar.analytic_3_left`, `OAI.SharpPlanar.analytic_3_right`, `OAI.SharpPlanar.analytic_large`, `OAI.SharpPlanar.analytic_zero`, `OAI.SharpPlanar.halfSign_1_N0_right`, `OAI.SharpPlanar.halfSign_1_N1_left`, `OAI.SharpPlanar.halfSign_1_N1_right`, `OAI.SharpPlanar.halfSign_4_N0_left`, `OAI.SharpPlanar.halfSign_4_N0_right`, `OAI.SharpPlanar.halfSign_4_N1_left` and `OAI.SharpPlanar.halfSign_4_N1_right` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HalfGapAnalytic.lean (declaration OAI.SharpPlanar.halfGap_segment_lower)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfGap_segment_lower {v m y s N : ℝ} (hv : v  ∈  Set.Icc 0 1)
    (hm : N ≤ m) (hy : N ≤ m+y) (hs : s ∈ Set.uIcc m (m+y*v)) : N ≤ s := by
  sorry
end SharpPlanar

end OAI
end
