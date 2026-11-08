-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_6_contains_g
-- name    : OAI.SharpPlanar.CachedData.mpower0_6_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T20:53:48.846045+00:00
-- url     : https://prove2.me/theorems/7a844cac-8c6c-4656-9440-bddce252738c
-- title:
--   OAI.SharpPlanar.CachedData.mpower0_6_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.mpower0_6_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma mpower0_6_contains_g (j : Fin 6) (i k : Fin 16) :
--       (mpower0_6 j i k).Contains (momentPower 6 ((quadraturePoint j.val (16*i.val+k.val))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.momentPower` (definitions bundle `OAIQ098G1643` of this split); `OAI.SharpPlanar.CachedData.mpower0_6` (definitions bundle `OAIQ098G431` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein33.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein36.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein36.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein36.N1_left.ts_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.ts_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein37.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein39.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein40.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein4.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein4.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein4.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein9.N1_right.t4_contains_g`, `OAI.SharpPlanar.CachedData.hk16_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm12_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm13_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm13_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm19_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm19_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm1_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm21_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm21_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm27_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm27_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm28_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm31_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm31_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm3_1_0_6.realContains_g` and `OAI.SharpPlanar.CachedData.mpower0_7_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean (declaration OAI.SharpPlanar.CachedData.mpower0_6_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G431
import Definitions.Def_OAIQ098G1643

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma mpower0_6_contains_g (j : Fin 6) (i k : Fin 16) :
    (mpower0_6 j i k).Contains (momentPower 6 ((quadraturePoint j.val (16*i.val+k.val)))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
