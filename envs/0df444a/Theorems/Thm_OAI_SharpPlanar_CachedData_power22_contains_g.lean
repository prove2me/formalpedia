-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power22_contains_g
-- name    : OAI.SharpPlanar.CachedData.power22_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:41:49.897283+00:00
-- url     : https://prove2.me/theorems/b3a9a4c0-f044-4b47-9984-8f42daa61341
-- title:
--   OAI.SharpPlanar.CachedData.power22_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power22_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power22_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power22 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(22:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.power22` (definitions bundle `OAIQ098G314` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein24.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N0_right.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t0_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t5_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t6_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t8_contains_g`, `OAI.SharpPlanar.Bernstein25.N1_right.t9_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hk24_0_7_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_5_contains_g`, `OAI.SharpPlanar.CachedData.hk25_0_6_contains_g`, `OAI.SharpPlanar.CachedData.hm24_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_0_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm24_1_0_5.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_0_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_0_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_1_0_3.realContains_g`, `OAI.SharpPlanar.CachedData.hm25_1_0_4.realContains_g`, `OAI.SharpPlanar.CachedData.power27_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm24_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm25_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U25.wuplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean (declaration OAI.SharpPlanar.CachedData.power22_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G314

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power22_contains_g (j : Fin 6) (i k : Fin 16) :
    (power22 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(22:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
