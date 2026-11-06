-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_trans24_contains_e
-- name    : OAI.SharpPlanar.CachedData.trans24_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T23:51:45.93345+00:00
-- url     : https://prove2.me/theorems/e54610ae-40d8-4fec-96de-97f452609687
-- title:
--   OAI.SharpPlanar.CachedData.trans24_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.trans24_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers30.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers30.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma trans24_contains_e (j : Fin 6) (i k : Fin 16) :
--       (trans24 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(24:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.trans24` (definitions bundle `OAIQ098E215` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein24.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein24.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein24.N1_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein25.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein25.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein27.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein27.N1_right.t6_contains_e`, `OAI.SharpPlanar.CachedData.hk27_1_3_contains_e`, `OAI.SharpPlanar.CachedData.hm24_0_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm24_0_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm24_1_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm25_0_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm25_0_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm25_0_1_7.realContains_e`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm25_1_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm25_1_1_7.realContains_e`, `OAI.SharpPlanar.CachedData.hm27_0_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm27_0_1_6.realContains_e`, `OAI.SharpPlanar.CachedData.hm27_0_1_7.contains_e`, `OAI.SharpPlanar.CachedData.hm27_0_1_9.realContains_e`, `OAI.SharpPlanar.CachedData.hm27_1_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm27_1_1_6.realContains_e`, `OAI.SharpPlanar.CachedData.hm27_1_1_7.contains_e`, `OAI.SharpPlanar.CachedData.hm27_1_1_9.realContains_e`, `OAI.SharpPlanar.CachedData.kernel28_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel31_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel31_1_contains_e`, `OAI.SharpPlanar.CachedData.trans32_contains_e`, `OAI.SharpPlanar.Residual24.bound0_0_e`, `OAI.SharpPlanar.Residual24.bound0_1_e`, `OAI.SharpPlanar.Residual24.bound1_0_e`, `OAI.SharpPlanar.Residual24.bound1_1_e`, `OAI.SharpPlanar.Residual25.bound0_0_e`, `OAI.SharpPlanar.Residual25.bound0_1_e`, `OAI.SharpPlanar.Residual25.bound1_0_e`, `OAI.SharpPlanar.Residual25.bound1_1_e`, `OAI.SharpPlanar.Residual27.bound0_0_e`, `OAI.SharpPlanar.Residual27.bound0_1_e`, `OAI.SharpPlanar.Residual27.bound1_0_e`, `OAI.SharpPlanar.Residual27.bound1_1_e`, `OAI.SharpPlanar.Residual28.bound0_1_e` and `OAI.SharpPlanar.Residual28.bound1_1_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers30.lean (declaration OAI.SharpPlanar.CachedData.trans24_contains)

import Mathlib
import Definitions.Def_OAIQ098E215

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans24_contains_e (j : Fin 6) (i k : Fin 16) :
    (trans24 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(24:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
