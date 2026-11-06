-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power80_contains_e
-- name    : OAI.SharpPlanar.CachedData.power80_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T23:49:32.068215+00:00
-- url     : https://prove2.me/theorems/51f8d4b7-b84d-4a17-952c-aaa4d2ca3b28
-- title:
--   OAI.SharpPlanar.CachedData.power80_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power80_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power80_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power80 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(80:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power80` (definitions bundle `OAIQ098E120` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.cm81_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm81_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column84_0_contains_e`, `OAI.SharpPlanar.CachedData.column84_1_contains_e`, `OAI.SharpPlanar.CachedData.column85_0_contains_e`, `OAI.SharpPlanar.CachedData.column85_1_contains_e`, `OAI.SharpPlanar.CachedData.power87_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm81_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U81.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U81.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U81.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean (declaration OAI.SharpPlanar.CachedData.power80_contains)

import Mathlib
import Definitions.Def_OAIQ098E120

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power80_contains_e (j : Fin 6) (i k : Fin 16) :
    (power80 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(80:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
