-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_widen_contains_g
-- name    : OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T18:18:04.232214+00:00
-- url     : https://prove2.me/theorems/bef8fb7c-00db-4fa1-85d9-c56eeb9e1b12
-- title:
--   OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma CBox.widen_contains_g {a c : CBox} {z w : ℂ} {n : ℤ} (hz : a.Contains z)
--       (herr : (precision:ℝ)*‖w-z‖ ≤ (n:ℝ)) (hc : a.WidenCheck c n) : c.Contains w
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` and `OAI.SharpPlanar.IntegerIntervals.precision` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` and `OAI.SharpPlanar.IntegerIntervals.CBox.WidenCheck` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerIntervals.exp_from_horner_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains)

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

lemma CBox.widen_contains_g {a c : CBox} {z w : ℂ} {n : ℤ} (hz : a.Contains z)
    (herr : (precision:ℝ)*‖w-z‖ ≤ (n:ℝ)) (hc : a.WidenCheck c n) : c.Contains w := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
