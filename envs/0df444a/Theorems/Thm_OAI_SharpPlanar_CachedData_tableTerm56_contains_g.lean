-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm56_contains_g
-- name    : OAI.SharpPlanar.CachedData.tableTerm56_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T18:26:09.566104+00:00
-- url     : https://prove2.me/theorems/01c90e77-6fe7-4e80-9e0e-d8cf9248b42a
-- title:
--   OAI.SharpPlanar.CachedData.tableTerm56_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.tableTerm56_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableDensityExpr.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableDensityExpr.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma tableTerm56_contains_g (a d : Bool) (j : Fin 6) (i k : Fin 16) :
--       (tableTerm a d 56 j i k).Contains (((if d then (tableD a 56:ℝ) else (tableC a 56:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 56 j.val (quadraturePoint j.val (16*i.val+k.val))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.tableC` and `OAI.SharpPlanar.tableD` (definitions bundle `OAIQ098G015` of this split); `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.basisFunction` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.tableTerm` (definitions bundle `OAIQ098G397` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.density1_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableDensityExpr.lean (declaration OAI.SharpPlanar.CachedData.tableTerm56_contains)

import Mathlib
import Definitions.Def_OAIQ098G397

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma tableTerm56_contains_g (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 56 j i k).Contains (((if d then (tableD a 56:ℝ) else (tableC a 56:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 56 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
