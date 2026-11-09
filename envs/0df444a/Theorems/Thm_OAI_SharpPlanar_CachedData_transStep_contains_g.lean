-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_contains_g
-- name    : OAI.SharpPlanar.CachedData.transStep_contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-08T21:54:19.82395+00:00
-- url     : https://prove2.me/theorems/5be704db-a97e-4bd1-a088-7bfce869110b
-- title:
--   OAI.SharpPlanar.CachedData.transStep_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.transStep_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact`):
--
--   ```lean
--   lemma transStep_contains_g (j : Fin 6) (i k : Fin 16) :
--       (transStep j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.z` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.CachedData.transStep` (definitions bundle `OAIQ098G064` of this split); `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.CachedData.kernel40_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel49_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel4_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel4_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel63_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel63_1_contains_g`, `OAI.SharpPlanar.CachedData.tm0_96_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_48_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_69_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_96_1.KContains_g`, `OAI.SharpPlanar.CachedData.trans29_contains_g`, `OAI.SharpPlanar.CachedData.trans32_contains_g`, `OAI.SharpPlanar.CachedData.trans36_contains_g`, `OAI.SharpPlanar.CachedData.trans38_contains_g`, `OAI.SharpPlanar.CachedData.trans39_contains_g`, `OAI.SharpPlanar.CachedData.trans3_contains_g`, `OAI.SharpPlanar.CachedData.trans43_contains_g`, `OAI.SharpPlanar.CachedData.trans47_contains_g`, `OAI.SharpPlanar.CachedData.trans49_contains_g`, `OAI.SharpPlanar.CachedData.trans50_contains_g`, `OAI.SharpPlanar.CachedData.trans51_contains_g`, `OAI.SharpPlanar.CachedData.trans52_contains_g`, `OAI.SharpPlanar.CachedData.trans53_contains_g`, `OAI.SharpPlanar.CachedData.trans55_contains_g`, `OAI.SharpPlanar.CachedData.trans57_contains_g`, `OAI.SharpPlanar.CachedData.trans61_contains_g`, `OAI.SharpPlanar.CachedData.trans64_contains_g`, `OAI.SharpPlanar.CachedData.trans67_contains_g`, `OAI.SharpPlanar.CachedData.trans69_contains_g`, `OAI.SharpPlanar.CachedData.trans71_contains_g`, `OAI.SharpPlanar.CachedData.trans72_contains_g`, `OAI.SharpPlanar.CachedData.trans74_contains_g`, `OAI.SharpPlanar.CachedData.trans75_contains_g`, `OAI.SharpPlanar.CachedData.trans76_contains_g`, `OAI.SharpPlanar.CachedData.trans78_contains_g`, `OAI.SharpPlanar.CachedData.trans81_contains_g`, `OAI.SharpPlanar.CachedData.trans84_contains_g`, `OAI.SharpPlanar.CachedData.trans86_contains_g`, `OAI.SharpPlanar.CachedData.trans88_contains_g`, `OAI.SharpPlanar.CachedData.trans91_contains_g`, `OAI.SharpPlanar.CachedData.trans95_contains_g`, `OAI.SharpPlanar.CachedData.trans97_contains_g` and `OAI.SharpPlanar.CachedData.trans99_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean (declaration OAI.SharpPlanar.CachedData.transStep_contains)

import Mathlib
import Definitions.Def_OAIQ098G064
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
lemma transStep_contains_g (j : Fin 6) (i k : Fin 16) :
    (transStep j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)))) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
