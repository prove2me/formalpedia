-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_36_1_KContains_g
-- name    : OAI.SharpPlanar.CachedData.tm1_36_1.KContains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-09T03:13:56.979295+00:00
-- url     : https://prove2.me/theorems/c1b7eaad-9a17-4bf0-997a-725b5021a0f4
-- title:
--   OAI.SharpPlanar.CachedData.tm1_36_1.KContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.tm1_36_1.KContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments36.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments36.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.tm1_36_1`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma KContains_g : realAnswer.Contains (tableMomentK true 36 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.tm1_36_1.realAnswer` (definitions bundle `OAIQ098G1552` of this split); `OAI.SharpPlanar.tableMomentK` (definitions bundle `OAIQ098G1682` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Residual36.bound0_1_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments36.lean (declaration OAI.SharpPlanar.CachedData.tm1_36_1.KContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1552
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_36_1
lemma KContains_g : realAnswer.Contains (tableMomentK true 36 1) := by
  sorry
end tm1_36_1

end SharpPlanar.CachedData

end OAI
end
