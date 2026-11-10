-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_column4_1_contains_g
-- name    : OAI.SharpPlanar.CachedData.column4_1_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T10:25:31.879046+00:00
-- url     : https://prove2.me/theorems/d580dca4-d7fb-498a-a396-6fd00a4710fb
-- title:
--   OAI.SharpPlanar.CachedData.column4_1_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.column4_1_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma column4_1_contains_g (j : Fin 6) (i k : Fin 16) :
--       (column4_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 4 j.val (quadraturePoint j.val (16*i.val+k.val)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.CachedData.column4_1` (definitions bundle `OAIQ098G047` of this split); `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.basisFunction` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.lentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_g` and `OAI.SharpPlanar.Numerical.lentry2_5_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean (declaration OAI.SharpPlanar.CachedData.column4_1_contains)

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column4_1_contains_g (j : Fin 6) (i k : Fin 16) :
    (column4_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 4 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
