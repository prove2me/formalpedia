-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_trans15_contains_g
-- name    : OAI.SharpPlanar.CachedData.trans15_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-09T04:22:12.645879+00:00
-- url     : https://prove2.me/theorems/a7992a4d-cc30-428b-a37d-44ac723af490
-- title:
--   OAI.SharpPlanar.CachedData.trans15_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.trans15_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma trans15_contains_g (j : Fin 6) (i k : Fin 16) :
--       (trans15 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(15:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.trans15` (definitions bundle `OAIQ098G302` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein15.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein15.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein15.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein15.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein15.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t7_contains_g`, `OAI.SharpPlanar.CachedData.cm1_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.hk15_1_9_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_8_contains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_10.contains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_7.contains_g`, `OAI.SharpPlanar.CachedData.hm15_0_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_10.contains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_7.contains_g`, `OAI.SharpPlanar.CachedData.hm15_1_1_8.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_7.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_7.realContains_g`, `OAI.SharpPlanar.CachedData.kernel16_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel19_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel21_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel21_1_contains_g`, `OAI.SharpPlanar.CachedData.trans22_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_5_contains_g`, `OAI.SharpPlanar.Residual15.bound0_0_g`, `OAI.SharpPlanar.Residual15.bound0_1_g`, `OAI.SharpPlanar.Residual15.bound1_0_g`, `OAI.SharpPlanar.Residual15.bound1_1_g`, `OAI.SharpPlanar.Residual16.bound0_0_g`, `OAI.SharpPlanar.Residual16.bound0_1_g`, `OAI.SharpPlanar.Residual16.bound1_0_g`, `OAI.SharpPlanar.Residual16.bound1_1_g`, `OAI.SharpPlanar.Residual19.bound0_1_g` and `OAI.SharpPlanar.Residual19.bound1_1_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean (declaration OAI.SharpPlanar.CachedData.trans15_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G302

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma trans15_contains_g (j : Fin 6) (i k : Fin 16) :
    (trans15 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(15:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
