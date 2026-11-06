-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_PointBox_calc_contains_e
-- name    : OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T23:15:24.561577+00:00
-- url     : https://prove2.me/theorems/57672bcd-0448-4426-aeca-f6edd7ea5631
-- title:
--   OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma PointBox.calc_contains_e {a : RBox} {x : ℝ} (hx : a.Contains x)
--       (hc : PointBox.Check a) : (PointBox.calc a).Contains x
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.IntegerIntervals.PointBox.Check`, `OAI.SharpPlanar.IntegerIntervals.PointBox.Contains` and `OAI.SharpPlanar.IntegerIntervals.PointBox.calc` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.atomPoint0_contains_e`, `OAI.SharpPlanar.CachedData.atomPoint1_contains_e`, `OAI.SharpPlanar.CachedData.atomPoint2_contains_e`, `OAI.SharpPlanar.CachedData.atomPoint3_contains_e`, `OAI.SharpPlanar.CachedData.atomPoint4_contains_e`, `OAI.SharpPlanar.CachedData.atomPoint5_contains_e`, `OAI.SharpPlanar.CachedData.atomPoint6_contains_e`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_e`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row1_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_e`, `OAI.SharpPlanar.IntegerGrid.row2_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row3_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_e`, `OAI.SharpPlanar.IntegerGrid.row4_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_e`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_e` and `OAI.SharpPlanar.IntegerGrid.row5_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.PointBox.calc_contains)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma PointBox.calc_contains_e {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : PointBox.Check a) : (PointBox.calc a).Contains x := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
