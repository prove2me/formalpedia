-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power30_contains_g
-- name    : OAI.SharpPlanar.CachedData.power30_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:41:51.428647+00:00
-- url     : https://prove2.me/theorems/4f7e3de4-2617-4553-8f05-e179109d48ef
-- title:
--   OAI.SharpPlanar.CachedData.power30_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power30_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power30_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power30 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(30:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.power30` (definitions bundle `OAIQ098G319` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein31.N0_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein31.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t1_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t1_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk33_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hm31_0_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm31_1_0_6.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_1_0_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm33_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.power36_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm31_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm33_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U31.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U31.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U33.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U33.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U33.wuminus_contains_g` and `OAI.SharpPlanar.Numerical.U33.wuplus_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean (declaration OAI.SharpPlanar.CachedData.power30_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G319

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power30_contains_g (j : Fin 6) (i k : Fin 16) :
    (power30 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(30:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
