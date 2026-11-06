-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_check_e
-- name    : OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:46:23.487999+00:00
-- url     : https://prove2.me/theorems/43031c29-997c-4e9d-9ca0-df78ba2bbf82
-- title:
--   OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.RBox.rat_check` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma RBox.rat_check_e (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).RatCheck m n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.rat` (definitions bundle `OAIQ098E026` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.RatCheck` (definitions bundle `OAIQ098E030` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.rat_check_e` and `OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.RBox.rat_check)

import Mathlib
import Definitions.Def_OAIQ098E026
import Definitions.Def_OAIQ098E030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma RBox.rat_check_e (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).RatCheck m n := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
