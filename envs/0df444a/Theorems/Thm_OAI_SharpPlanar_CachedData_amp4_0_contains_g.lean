-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_amp4_0_contains_g
-- name    : OAI.SharpPlanar.CachedData.amp4_0_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T19:53:24.983428+00:00
-- url     : https://prove2.me/theorems/6be3d4d2-97b9-4a73-9c23-8e6f0c23bd80
-- title:
--   OAI.SharpPlanar.CachedData.amp4_0_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.amp4_0_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma amp4_0_contains_g (j : Fin 6) (i k : Fin 16) :
--       (amp4_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 4 j.val (quadraturePoint j.val (16*i.val+k.val)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.CachedData.amp4_0` (definitions bundle `OAIQ098G021` of this split); `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.waveAmplitude` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_g`, `OAI.SharpPlanar.CachedData.column100_0_contains_g`, `OAI.SharpPlanar.CachedData.column52_0_contains_g`, `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm16_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm28_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm40_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm4_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm64_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm88_contains_g`, `OAI.SharpPlanar.Numerical.Lmat_column_g`, `OAI.SharpPlanar.Numerical.U16.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U16.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U16.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U28.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U40.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U40.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U64.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U64.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U64.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U64.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U88.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U88.wuplus_column_g`, `OAI.SharpPlanar.Numerical.defectminus_column_g`, `OAI.SharpPlanar.Numerical.defectplus_column_g`, `OAI.SharpPlanar.Numerical.dentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_g` and `OAI.SharpPlanar.Numerical.lentry8_2_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean (declaration OAI.SharpPlanar.CachedData.amp4_0_contains)

import Mathlib
import Definitions.Def_OAIQ098G021
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
lemma amp4_0_contains_g (j : Fin 6) (i k : Fin 16) :
    (amp4_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 4 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
