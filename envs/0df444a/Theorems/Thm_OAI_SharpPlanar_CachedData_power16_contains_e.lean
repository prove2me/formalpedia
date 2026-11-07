-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power16_contains_e
-- name    : OAI.SharpPlanar.CachedData.power16_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:15:58.058567+00:00
-- url     : https://prove2.me/theorems/67c51fda-4483-47f8-a95b-87159be72333
-- title:
--   OAI.SharpPlanar.CachedData.power16_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power16_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power16_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power16 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(16:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power16` (definitions bundle `OAIQ098E089` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein16.N0_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein16.N1_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein19.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein19.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.column19_0_contains_e`, `OAI.SharpPlanar.CachedData.column19_1_contains_e`, `OAI.SharpPlanar.CachedData.hk19_0_5_contains_e`, `OAI.SharpPlanar.CachedData.hm16_0_0_5.realContains_e`, `OAI.SharpPlanar.CachedData.hm16_1_0_5.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_0_13.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_0_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_0_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_0_0_8.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_0_13.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_0_3.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_0_4.realContains_e`, `OAI.SharpPlanar.CachedData.hm19_1_0_8.realContains_e`, `OAI.SharpPlanar.CachedData.power21_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm16_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U16.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U16.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean (declaration OAI.SharpPlanar.CachedData.power16_contains)

import Mathlib
import Definitions.Def_OAIQ098E031
import Definitions.Def_OAIQ098E089

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power16_contains_e (j : Fin 6) (i k : Fin 16) :
    (power16 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(16:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
