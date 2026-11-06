-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_trans16_contains_e
-- name    : OAI.SharpPlanar.CachedData.trans16_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T04:50:56.893097+00:00
-- url     : https://prove2.me/theorems/a49a7e0f-a4b7-4f43-9826-8c30cbc2bb60
-- title:
--   OAI.SharpPlanar.CachedData.trans16_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.trans16_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma trans16_contains_e (j : Fin 6) (i k : Fin 16) :
--       (trans16 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(16:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.trans16` (definitions bundle `OAIQ098E105` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein16.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t6_contains_e`, `OAI.SharpPlanar.CachedData.hk19_1_3_contains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_12.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_13.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_0_1_8.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_12.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_13.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_1_8.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_10.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_11.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_12.contains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_6.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_7.contains_e`, `OAI.SharpPlanar.CachedData.hm19_0_1_9.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_10.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_11.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_12.contains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_6.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_7.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_1_9.realContains_e`, `OAI.SharpPlanar.CachedData.kernel21_0_contains_e`, `OAI.SharpPlanar.CachedData.trans24_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_5_contains_e`, `OAI.SharpPlanar.Residual16.bound0_0_e`, `OAI.SharpPlanar.Residual16.bound0_1_e`, `OAI.SharpPlanar.Residual16.bound1_0_e`, `OAI.SharpPlanar.Residual16.bound1_1_e`, `OAI.SharpPlanar.Residual19.bound0_0_e`, `OAI.SharpPlanar.Residual19.bound0_1_e`, `OAI.SharpPlanar.Residual19.bound1_0_e`, `OAI.SharpPlanar.Residual19.bound1_1_e`, `OAI.SharpPlanar.Residual21.bound0_1_e` and `OAI.SharpPlanar.Residual21.bound1_1_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean (declaration OAI.SharpPlanar.CachedData.trans16_contains)

import Mathlib
import Definitions.Def_OAIQ098E105

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans16_contains_e (j : Fin 6) (i k : Fin 16) :
    (trans16 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(16:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
