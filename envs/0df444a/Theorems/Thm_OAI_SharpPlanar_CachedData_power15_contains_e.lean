-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power15_contains_e
-- name    : OAI.SharpPlanar.CachedData.power15_contains_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T20:29:47.417646+00:00
-- url     : https://prove2.me/theorems/0ff42a99-7930-40c6-b854-98aaad125457
-- title:
--   OAI.SharpPlanar.CachedData.power15_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power15_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power15_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power15 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(15:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power15` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein15.N0_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein15.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t10_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t1_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t7_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t10_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t1_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t7_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein15.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.power16_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm15_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U15.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U15.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U15.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers20.lean (declaration OAI.SharpPlanar.CachedData.power15_contains)

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
lemma power15_contains_e (j : Fin 6) (i k : Fin 16) :
    (power15 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(15:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
