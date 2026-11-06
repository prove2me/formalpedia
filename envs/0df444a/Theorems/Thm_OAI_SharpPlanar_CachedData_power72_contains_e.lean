-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power72_contains_e
-- name    : OAI.SharpPlanar.CachedData.power72_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T22:17:36.488067+00:00
-- url     : https://prove2.me/theorems/5338e26a-205d-4126-b174-65483b45ee36
-- title:
--   OAI.SharpPlanar.CachedData.power72_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power72_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power72_contains_e (j : Fin 6) (i k : Fin 16) :
--       (power72 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(72:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split); `OAI.SharpPlanar.CachedData.power72` (definitions bundle `OAIQ098E099` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.cm73_1_0_1.contains_e`, `OAI.SharpPlanar.CachedData.cm73_1_1_1.contains_e`, `OAI.SharpPlanar.CachedData.column75_0_contains_e`, `OAI.SharpPlanar.CachedData.column75_1_contains_e`, `OAI.SharpPlanar.CachedData.column76_0_contains_e`, `OAI.SharpPlanar.CachedData.column76_1_contains_e`, `OAI.SharpPlanar.CachedData.power79_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm72_contains_e`, `OAI.SharpPlanar.CachedData.tableTerm73_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry1_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry2_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry5_0_contains_e`, `OAI.SharpPlanar.Numerical.U72.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U72.wuminus_column_e`, `OAI.SharpPlanar.Numerical.U72.wuplus_column_e`, `OAI.SharpPlanar.Numerical.U73.entry0_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry0_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry1_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry2_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry3_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry3_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry4_0_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry4_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.entry5_1_contains_e`, `OAI.SharpPlanar.Numerical.U73.wuminus_column_e` and `OAI.SharpPlanar.Numerical.U73.wuplus_column_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers80.lean (declaration OAI.SharpPlanar.CachedData.power72_contains)

import Mathlib
import Definitions.Def_OAIQ098E031
import Definitions.Def_OAIQ098E099

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power72_contains_e (j : Fin 6) (i k : Fin 16) :
    (power72 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(72:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
