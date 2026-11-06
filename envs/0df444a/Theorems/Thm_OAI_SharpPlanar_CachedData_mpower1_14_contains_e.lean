-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_14_contains_e
-- name    : OAI.SharpPlanar.CachedData.mpower1_14_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T00:03:15.710593+00:00
-- url     : https://prove2.me/theorems/087250ba-8dbb-481d-8d4a-75e947142a1b
-- title:
--   OAI.SharpPlanar.CachedData.mpower1_14_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower1_14_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower1_14_contains_e (j : Fin 6) (i k : Fin 16) :
--       (mpower1_14 j i k).Contains (momentPower 14 (z (quadraturePoint j.val (16*i.val+k.val))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.mpower1_14` (definitions bundle `OAIQ098E148` of this split); `OAI.SharpPlanar.momentPower` (definitions bundle `OAIQ098E229` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein1.N0_right.t13_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein4.N0_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein4.N0_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein4.N1_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein4.N1_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein7.N0_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein7.N0_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein7.N1_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein7.N1_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t12_contains_e`, `OAI.SharpPlanar.CachedData.hk0_1_14_contains_e` and `OAI.SharpPlanar.CachedData.mpower1_15_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers15.lean (declaration OAI.SharpPlanar.CachedData.mpower1_14_contains)

import Mathlib
import Definitions.Def_OAIQ098E148
import Definitions.Def_OAIQ098E229

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower1_14_contains_e (j : Fin 6) (i k : Fin 16) :
    (mpower1_14 j i k).Contains (momentPower 14 (z (quadraturePoint j.val (16*i.val+k.val)))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
