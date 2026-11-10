-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_power54_contains_g
-- name    : OAI.SharpPlanar.CachedData.power54_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:20:40.401205+00:00
-- url     : https://prove2.me/theorems/40678888-864c-401d-82fa-a731cb1b4fe9
-- title:
--   OAI.SharpPlanar.CachedData.power54_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.power54_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Powers60.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers60.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma power54_contains_g (j : Fin 6) (i k : Fin 16) :
--       (power54 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(54:ℕ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.power54` (definitions bundle `OAIQ098G331` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.column60_0_contains_g`, `OAI.SharpPlanar.CachedData.column60_1_contains_g`, `OAI.SharpPlanar.CachedData.power61_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm55_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm57_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U55.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U55.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuminus_contains_g` and `OAI.SharpPlanar.Numerical.U57.wuplus_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers60.lean (declaration OAI.SharpPlanar.CachedData.power54_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G331

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power54_contains_g (j : Fin 6) (i k : Fin 16) :
    (power54 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(54:ℕ))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
