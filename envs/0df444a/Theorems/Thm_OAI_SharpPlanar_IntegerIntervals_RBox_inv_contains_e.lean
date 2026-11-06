-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_inv_contains_e
-- name    : OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T06:02:11.968842+00:00
-- url     : https://prove2.me/theorems/1501c077-373a-4b31-ba44-241dbc6a4ff0
-- title:
--   OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma RBox.inv_contains_e {a c : RBox} {x : ℝ} (hx : a.Contains x)
--       (hc : a.InvCheck c) : c.Contains x⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098E028` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.InvCheck` (definitions bundle `OAIQ098E030` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_e` and `OAI.SharpPlanar.Numerical.qiBox_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.RBox.inv_contains)

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

lemma RBox.inv_contains_e {a c : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : a.InvCheck c) : c.Contains x⁻¹ := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
