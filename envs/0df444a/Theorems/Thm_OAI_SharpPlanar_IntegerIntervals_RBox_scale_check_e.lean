-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_check_e
-- name    : OAI.SharpPlanar.IntegerIntervals.RBox.scale_check_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:46:43.805182+00:00
-- url     : https://prove2.me/theorems/7c4487b1-5210-4390-b6f4-e5e8344ca370
-- title:
--   OAI.SharpPlanar.IntegerIntervals.RBox.scale_check_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.RBox.scale_check` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma RBox.scale_check_e (a : RBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` and `OAI.SharpPlanar.IntegerIntervals.RBox.scale` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.ScaleCheck` (definitions bundle `OAIQ098E030` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_e` and `OAI.SharpPlanar.IntegerIntervals.RBox.contains_scale_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.RBox.scale_check)

import Mathlib
import Definitions.Def_OAIQ098E030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma RBox.scale_check_e (a : RBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
