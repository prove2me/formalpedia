-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_contains_e
-- name    : OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T06:03:09.118712+00:00
-- url     : https://prove2.me/theorems/006b9bdb-9fc8-4771-85ff-fdcc4be9a0d7
-- title:
--   OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma RBox.rat_contains_e {a : RBox} {m n : ℤ} (h : a.RatCheck m n) :
--       a.Contains ((m:ℝ)/n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.RatCheck` (definitions bundle `OAIQ098E030` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_e` and `OAI.SharpPlanar.IntegerIntervals.RBox.contains_rat_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains)

import Mathlib
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma RBox.rat_contains_e {a : RBox} {m n : ℤ} (h : a.RatCheck m n) :
    a.Contains ((m:ℝ)/n) := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
