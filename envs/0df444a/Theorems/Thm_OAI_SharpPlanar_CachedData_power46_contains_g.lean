-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power46_contains_g
-- name    : OAI.SharpPlanar.CachedData.power46_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:22:42.192642+00:00
-- url     : https://prove2.me/theorems/b9e67ef4-bd95-4bda-a9e2-a483da8efc70
-- title:
--   OAI.SharpPlanar.CachedData.power46_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power46_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power46_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power46 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(46:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.power46` (definitions bundle `OAIQ098G327` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.column51_0_contains_g`, `OAI.SharpPlanar.CachedData.column51_1_contains_g`, `OAI.SharpPlanar.CachedData.column52_0_contains_g`, `OAI.SharpPlanar.CachedData.column52_1_contains_g`, `OAI.SharpPlanar.CachedData.power54_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm48_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm49_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U48.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U49.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U49.wuplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean (declaration OAI.SharpPlanar.CachedData.power46_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G327

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power46_contains_g (j : Fin 6) (i k : Fin 16) :
    (power46 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(46:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
