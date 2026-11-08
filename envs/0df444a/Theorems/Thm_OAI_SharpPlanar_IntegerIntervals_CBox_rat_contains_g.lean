-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_g
-- name    : OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T18:12:21.519627+00:00
-- url     : https://prove2.me/theorems/72ec4173-918a-4b21-bc9e-e9d697dc5304
-- title:
--   OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma CBox.rat_contains_g {a : CBox} {mr nr mi ni : ℤ} (h : a.RatCheck mr nr mi ni) :
--       a.Contains ((mr:ℂ)/nr + (mi:ℂ)/ni*Complex.I)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` and `OAI.SharpPlanar.IntegerIntervals.CBox.RatCheck` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_contains_g`, `OAI.SharpPlanar.IntegerIntervals.CBox.contains_rat_g` and `OAI.SharpPlanar.IntegerIntervals.horner_step_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains)

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

lemma CBox.rat_contains_g {a : CBox} {mr nr mi ni : ℤ} (h : a.RatCheck mr nr mi ni) :
    a.Contains ((mr:ℂ)/nr + (mi:ℂ)/ni*Complex.I) := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
