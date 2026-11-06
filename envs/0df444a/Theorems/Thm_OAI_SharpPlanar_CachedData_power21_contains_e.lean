-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power21_contains_e
-- name    : OAI.SharpPlanar.CachedData.power21_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T22:16:06.723087+00:00
-- url     : https://prove2.me/theorems/5641e4c2-7eb5-4145-849e-796f2828f29a
-- title:
--   OAI.SharpPlanar.CachedData.power21_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power21_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power21_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power21 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(21:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power21` (definitions bundle `OAIQ098E090` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein21.N0_left.bound_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.bound_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein21.N0_right.t9_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.bound_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t0_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t3_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t4_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t5_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t6_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t8_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_left.t9_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.bound_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t0_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t2_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t3_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t4_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t5_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t6_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t8_contains_e`, `OAI.SharpPlanar.Bernstein21.N1_right.t9_contains_e`, `OAI.SharpPlanar.CachedData.column21_1_contains_e`, `OAI.SharpPlanar.CachedData.hk21_0_12_contains_e`, `OAI.SharpPlanar.CachedData.hk21_0_13_contains_e`, `OAI.SharpPlanar.CachedData.hk21_0_3_contains_e`, `OAI.SharpPlanar.CachedData.hm21_0_0_2.realContains_e`, `OAI.SharpPlanar.CachedData.power24_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm21_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U21.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U21.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers30.lean (declaration OAI.SharpPlanar.CachedData.power21_contains)

import Mathlib
import Definitions.Def_OAIQ098E031
import Definitions.Def_OAIQ098E090

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power21_contains_e (j : Fin 6) (i k : Fin 16) :
    (power21 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(21:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
