-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_column4_0_contains_e
-- name    : OAI.SharpPlanar.CachedData.column4_0_contains_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T22:11:00.804961+00:00
-- url     : https://prove2.me/theorems/292b2a72-e299-47fd-aa92-0865369dcb98
-- title:
--   OAI.SharpPlanar.CachedData.column4_0_contains_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.column4_0_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma column4_0_contains_e (j : Fin 6) (i k : Fin 16) :
--       (column4_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 4 j.val (quadraturePoint j.val (16*i.val+k.val)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.basisFunction` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098E018` of this split); `OAI.SharpPlanar.CachedData.column4_0` (definitions bundle `OAIQ098E025` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098E031` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.tableTerm4_contains_e`, `OAI.SharpPlanar.Numerical.Lmat_column_e`, `OAI.SharpPlanar.Numerical.defectminus_norm_e`, `OAI.SharpPlanar.Numerical.defectplus_norm_e`, `OAI.SharpPlanar.Numerical.dentry0_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry0_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry6_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_e`, `OAI.SharpPlanar.Numerical.lentry8_2_contains_e` and `OAI.SharpPlanar.Numerical.lentry9_2_contains_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean (declaration OAI.SharpPlanar.CachedData.column4_0_contains)

import Mathlib
import Definitions.Def_OAIQ098E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column4_0_contains_e (j : Fin 6) (i k : Fin 16) :
    (column4_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 4 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
