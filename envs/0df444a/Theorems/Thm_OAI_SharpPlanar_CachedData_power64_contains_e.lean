-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power64_contains_e
-- name    : OAI.SharpPlanar.CachedData.power64_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T20:33:06.945961+00:00
-- url     : https://prove2.me/theorems/f9135b2f-075c-493b-b157-3710c24cc503
-- title:
--   OAI.SharpPlanar.CachedData.power64_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power64_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers70.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers70.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power64_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power64 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(64:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power64` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.column67_0_contains_e`, `OAI.SharpPlanar.CachedData.column67_1_contains_e`, `OAI.SharpPlanar.CachedData.column69_0_contains_e`, `OAI.SharpPlanar.CachedData.column69_1_contains_e`, `OAI.SharpPlanar.CachedData.power72_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm64_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U64.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U64.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U64.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers70.lean (declaration OAI.SharpPlanar.CachedData.power64_contains)

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
lemma power64_contains_e (j : Fin 6) (i k : Fin 16) :
    (power64 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(64:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
