-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power1_contains_e
-- name    : OAI.SharpPlanar.CachedData.power1_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:37:30.654411+00:00
-- url     : https://prove2.me/theorems/c97ecd89-6aba-42e6-8c76-c5f60d538358
-- title:
--   OAI.SharpPlanar.CachedData.power1_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power1_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power1 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(1:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.CachedData.power1` and `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein1.N0_right.bound22_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound23_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound24_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound25_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound26_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound27_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound28_e`, `OAI.SharpPlanar.Bernstein1.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t12_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t17_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t18_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t19_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t20_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t21_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t22_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t28_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein1.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t16_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t17_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t18_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t19_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t20_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t21_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t27_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t28_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t16_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t17_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t18_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t19_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t20_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t21_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t27_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t28_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein1.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.cm1_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column1_0_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_17_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_27_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_28_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_7_contains_e`, `OAI.SharpPlanar.CachedData.hk1_0_8_contains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_14.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_15.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_16.contains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_24.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_25.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_26.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_5.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_0_0_6.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_14.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_15.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_16.contains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_24.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_25.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_26.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_5.realContains_e`, `OAI.SharpPlanar.CachedData.hm1_1_0_6.realContains_e`, `OAI.SharpPlanar.CachedData.power3_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm1_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_3_contains_e` and `OAI.SharpPlanar.Numerical.lentry9_3_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean (declaration OAI.SharpPlanar.CachedData.power1_contains)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power1_contains_e (j : Fin 6) (i k : Fin 16) :
    (power1 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(1:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
