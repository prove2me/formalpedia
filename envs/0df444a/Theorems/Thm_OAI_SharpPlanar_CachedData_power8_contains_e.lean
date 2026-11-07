-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power8_contains_e
-- name    : OAI.SharpPlanar.CachedData.power8_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T20:39:28.335531+00:00
-- url     : https://prove2.me/theorems/2055f8f2-3382-4866-8433-e94836c9cf5a
-- title:
--   OAI.SharpPlanar.CachedData.power8_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power8_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power8_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power8 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(8:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power8` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein12.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein12.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t13_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein9.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.cm9_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm9_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column12_0_contains_e`, `OAI.SharpPlanar.CachedData.column12_1_contains_e`, `OAI.SharpPlanar.CachedData.hk12_0_13_contains_e`, `OAI.SharpPlanar.CachedData.hk12_0_4_contains_e`, `OAI.SharpPlanar.CachedData.hk12_0_5_contains_e`, `OAI.SharpPlanar.CachedData.hm12_0_0_11.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_0_0_12.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_0_0_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_0_0_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_0_0_7.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_0_0_8.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_0_11.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_0_12.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_0_2.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_0_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_0_7.realContains_e`, `OAI.SharpPlanar.CachedData.hm12_1_0_8.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_0_13.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_0_14.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_0_0_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_0_13.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_0_14.realContains_e`, `OAI.SharpPlanar.CachedData.hm9_1_0_4.realContains_e`, `OAI.SharpPlanar.CachedData.power13_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm9_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U9.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean (declaration OAI.SharpPlanar.CachedData.power8_contains)

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
lemma power8_contains_e (j : Fin 6) (i k : Fin 16) :
    (power8 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(8:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
