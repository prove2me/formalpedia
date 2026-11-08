-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_g
-- name    : OAI.SharpPlanar.IntegerIntervals.RBox.add_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T18:30:15.135456+00:00
-- url     : https://prove2.me/theorems/fdbbfe13-29a5-481f-870e-ca094b645d33
-- title:
--   OAI.SharpPlanar.IntegerIntervals.RBox.add_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.RBox.add_contains` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma RBox.add_contains_g {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
--       (hc : a.AddCheck b c) : c.Contains (x+y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.AddCheck` (definitions bundle `OAIQ098G047` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_g`, `OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_g` and `OAI.SharpPlanar.IntegerIntervals.RBox.contains_add_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.RBox.add_contains)

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma RBox.add_contains_g {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
