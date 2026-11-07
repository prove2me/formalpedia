-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_trans8_contains_e
-- name    : OAI.SharpPlanar.CachedData.trans8_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T20:37:31.624317+00:00
-- url     : https://prove2.me/theorems/cc498f4f-5fd3-4960-86d2-14e2853fc51b
-- title:
--   OAI.SharpPlanar.CachedData.trans8_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.trans8_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma trans8_contains_e (j : Fin 6) (i k : Fin 16) :
--       (trans8 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(8:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.trans8` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein9.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t8_contains_e`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_1_12.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_1_7.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_1_11.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_1_12.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_1_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_1_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_1_7.realContains_e`, `OAI.SharpPlanar.CachedData.kernel12_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel12_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel13_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel13_1_contains_e`, `OAI.SharpPlanar.CachedData.kernel15_0_contains_e`, `OAI.SharpPlanar.CachedData.kernel15_1_contains_e`, `OAI.SharpPlanar.CachedData.trans16_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_0_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_5_contains_e`, `OAI.SharpPlanar.Residual9.bound0_0_e`, `OAI.SharpPlanar.Residual9.bound0_1_e`, `OAI.SharpPlanar.Residual9.bound1_0_e` and `OAI.SharpPlanar.Residual9.bound1_1_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean (declaration OAI.SharpPlanar.CachedData.trans8_contains)

import Mathlib
import Definitions.Def_OAIQ098E126

section

attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans8_contains_e (j : Fin 6) (i k : Fin 16) :
    (trans8 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(8:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
