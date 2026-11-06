-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_19_contains_e
-- name    : OAI.SharpPlanar.CachedData.mpower0_19_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T23:44:20.058031+00:00
-- url     : https://prove2.me/theorems/bc64b5b3-061d-4b4d-8969-a95d26351385
-- title:
--   OAI.SharpPlanar.CachedData.mpower0_19_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower0_19_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower0_19_contains_e (j : Fin 6) (i k : Fin 16) :
--       (mpower0_19 j i k).Contains (momentPower 19 ((quadraturePoint j.val (16*i.val+k.val))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.mpower0_19` (definitions bundle `OAIQ098E143` of this split); `OAI.SharpPlanar.momentPower` (definitions bundle `OAIQ098E229` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein0.N1_right.t20_contains_e`, `OAI.SharpPlanar.Bernstein0.N1_right.t21_contains_e`, `OAI.SharpPlanar.Bernstein0.N1_right.t22_contains_e`, `OAI.SharpPlanar.Bernstein0.N1_right.t23_contains_e`, `OAI.SharpPlanar.Bernstein0.N1_right.t24_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t18_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t19_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t20_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t21_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t22_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t17_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t18_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t19_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t20_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t21_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t17_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t18_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t19_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t20_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t21_contains_e`, `OAI.SharpPlanar.Bernstein4.N0_left.t17_contains_e`, `OAI.SharpPlanar.Bernstein4.N0_right.t17_contains_e`, `OAI.SharpPlanar.Bernstein4.N1_left.t17_contains_e`, `OAI.SharpPlanar.Bernstein4.N1_right.t17_contains_e`, `OAI.SharpPlanar.CachedData.hk0_0_19_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_27_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_28_contains_e`, `OAI.SharpPlanar.CachedData.hm0_1_0_25.realContains_e`, `OAI.SharpPlanar.CachedData.hm0_1_0_26.realContains_e`, `OAI.SharpPlanar.CachedData.hm0_1_0_27.realContains_e`, `OAI.SharpPlanar.CachedData.hm0_1_0_28.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_24.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_25.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_26.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_24.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_25.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_26.realContains_e` and `OAI.SharpPlanar.CachedData.mpower0_29_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers20.lean (declaration OAI.SharpPlanar.CachedData.mpower0_19_contains)

import Mathlib
import Definitions.Def_OAIQ098E143
import Definitions.Def_OAIQ098E229

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower0_19_contains_e (j : Fin 6) (i k : Fin 16) :
    (mpower0_19 j i k).Contains (momentPower 19 ((quadraturePoint j.val (16*i.val+k.val)))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
