-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_4_contains_e
-- name    : OAI.SharpPlanar.CachedData.mpower1_4_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T00:05:44.507198+00:00
-- url     : https://prove2.me/theorems/42f03987-8ca3-4888-9f0b-f1b613ed94ca
-- title:
--   OAI.SharpPlanar.CachedData.mpower1_4_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower1_4_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower1_4_contains_e (j : Fin 6) (i k : Fin 16) :
--       (mpower1_4 j i k).Contains (momentPower 4 (z (quadraturePoint j.val (16*i.val+k.val))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.mpower1_4` (definitions bundle `OAIQ098E154` of this split); `OAI.SharpPlanar.momentPower` (definitions bundle `OAIQ098E229` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein19.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein28.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein28.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein28.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein28.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein33.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein33.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein33.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein33.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein36.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein36.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein36.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein36.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein37.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein37.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein37.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein37.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein39.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein39.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein39.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein39.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein3.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein3.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein3.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein3.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein4.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein4.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein4.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein4.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein7.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein7.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein7.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein7.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein9.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein9.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein9.N1_right.bound_e`, `OAI.SharpPlanar.CachedData.hk1_1_4_contains_e`, `OAI.SharpPlanar.CachedData.hm0_0_1_4.contains_e`, `OAI.SharpPlanar.CachedData.hm12_0_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm13_0_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm13_1_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm15_0_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm15_1_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_4.realContains_e` and `OAI.SharpPlanar.CachedData.mpower1_5_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean (declaration OAI.SharpPlanar.CachedData.mpower1_4_contains)

import Mathlib
import Definitions.Def_OAIQ098E154
import Definitions.Def_OAIQ098E229

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower1_4_contains_e (j : Fin 6) (i k : Fin 16) :
    (mpower1_4 j i k).Contains (momentPower 4 (z (quadraturePoint j.val (16*i.val+k.val)))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
