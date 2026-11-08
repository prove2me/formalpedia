-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_inv_g
-- name    : OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:04:51.048429+00:00
-- url     : https://prove2.me/theorems/f5069d29-1965-47cd-ab2b-abb9dc43e1d7
-- title:
--   OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma CBox.contains_inv_g {a : CBox} {z : ℂ} (hz : a.Contains z)
--       (hi : ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
--         ((a.re.mul a.re).add (a.im.mul a.im)).inv) :
--       a.inv.Contains z⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` and `OAI.SharpPlanar.IntegerIntervals.RBox.add` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.inv` (definitions bundle `OAIQ098G031` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains`, `OAI.SharpPlanar.IntegerIntervals.RBox.InvCheck` and `OAI.SharpPlanar.IntegerIntervals.RBox.mul` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.inv` (definitions bundle `OAIQ098G087` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerIntervals.lamBox_contains_g` and `OAI.SharpPlanar.IntegerIntervals.zBox_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv)

import Mathlib
import Definitions.Def_OAIQ098G087

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_inv_g {a : CBox} {z : ℂ} (hz : a.Contains z)
    (hi : ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
      ((a.re.mul a.re).add (a.im.mul a.im)).inv) :
    a.inv.Contains z⁻¹ := by
  sorry

end SharpPlanar.IntegerIntervals

end OAI
end
