-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_inv_checked_e
-- name    : OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T23:13:49.290212+00:00
-- url     : https://prove2.me/theorems/541bcf48-ce3d-4759-8578-62a4a13bfbf7
-- title:
--   OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked` of [lean/OAI/Analysis/PlanarPacking/Intervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerIntervals`):
--
--   ```lean
--   lemma CBox.inv_checked_e {a c : CBox} {rr ii den dinv : RBox} {z : ℂ}
--       (hz : a.Contains z) (hrr : a.re.MulCheck a.re rr) (hii : a.im.MulCheck a.im ii)
--       (hs : rr.AddCheck ii den) (hi : den.InvCheck dinv)
--       (hr : a.re.MulCheck dinv c.re) (him : a.im.neg.MulCheck dinv c.im) :
--       c.Contains z⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox`, `OAI.SharpPlanar.IntegerIntervals.RBox` and `OAI.SharpPlanar.IntegerIntervals.RBox.neg` (definitions bundle `OAIQ098E017` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.AddCheck` (definitions bundle `OAIQ098E026` of this split); `OAI.SharpPlanar.IntegerIntervals.RBox.InvCheck` and `OAI.SharpPlanar.IntegerIntervals.RBox.MulCheck` (definitions bundle `OAIQ098E030` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerIntervals.CBox.contains_inv_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean (declaration OAI.SharpPlanar.IntegerIntervals.CBox.inv_checked)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
namespace IntegerIntervals

lemma CBox.inv_checked_e {a c : CBox} {rr ii den dinv : RBox} {z : ℂ}
    (hz : a.Contains z) (hrr : a.re.MulCheck a.re rr) (hii : a.im.MulCheck a.im ii)
    (hs : rr.AddCheck ii den) (hi : den.InvCheck dinv)
    (hr : a.re.MulCheck dinv c.re) (him : a.im.neg.MulCheck dinv c.im) :
    c.Contains z⁻¹ := by
  sorry

end IntegerIntervals
end SharpPlanar

end OAI
end
