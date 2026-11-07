-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power31_contains_e
-- name    : OAI.SharpPlanar.CachedData.power31_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T20:31:34.591941+00:00
-- url     : https://prove2.me/theorems/6e040b2b-cf38-4531-83dc-38eb58bcb439
-- title:
--   OAI.SharpPlanar.CachedData.power31_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power31_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power31_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power31 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(31:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power31` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein31.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein31.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t11_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t11_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein31.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.power32_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm31_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U31.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U31.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean (declaration OAI.SharpPlanar.CachedData.power31_contains)

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
lemma power31_contains_e (j : Fin 6) (i k : Fin 16) :
    (power31 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(31:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
