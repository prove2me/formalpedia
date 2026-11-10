-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_column28_1_contains_g
-- name    : OAI.SharpPlanar.CachedData.column28_1_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T20:03:10.909579+00:00
-- url     : https://prove2.me/theorems/6b750566-d72c-49b6-b859-0dfbcfab327b
-- title:
--   OAI.SharpPlanar.CachedData.column28_1_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.column28_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Columns30.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns30.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma column28_1_contains_g (j : Fin 6) (i k : Fin 16) :
--       (column28_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 28 j.val (quadraturePoint j.val (16*i.val+k.val)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.basisFunction` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.column28_1` (definitions bundle `OAIQ098G136` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.tableTerm28_contains_g`, `OAI.SharpPlanar.Numerical.U28.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U28.wuplus_column_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns30.lean (declaration OAI.SharpPlanar.CachedData.column28_1_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G136

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column28_1_contains_g (j : Fin 6) (i k : Fin 16) :
    (column28_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 28 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
