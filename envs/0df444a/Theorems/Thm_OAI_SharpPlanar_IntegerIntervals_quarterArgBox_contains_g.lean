-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_quarterArgBox_contains_g
-- name    : OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T09:25:32.898942+00:00
-- url     : https://prove2.me/theorems/e740cb89-3482-42b4-9644-0e39ba175658
-- title:
--   OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma quarterArgBox_contains_g {a : RBox} {x : ℝ} (hx : a.Contains x)
--       (hi : (denBox a).GoodInv) :
--       (quarterArgBox a).Contains (Complex.I*Real.pi*pointZ x/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.pointZ` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.denBox` (definitions bundle `OAIQ098G076` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` and `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.GoodInv` (definitions bundle `OAIQ098G087` of this split); `OAI.SharpPlanar.IntegerIntervals.quarterArgBox` (definitions bundle `OAIQ098G089` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G089

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma quarterArgBox_contains_g {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) :
    (quarterArgBox a).Contains (Complex.I*Real.pi*pointZ x/4) := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
