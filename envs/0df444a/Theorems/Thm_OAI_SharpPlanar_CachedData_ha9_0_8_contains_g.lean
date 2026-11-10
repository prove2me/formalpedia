-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_ha9_0_8_contains_g
-- name    : OAI.SharpPlanar.CachedData.ha9_0_8_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T08:24:33.894476+00:00
-- url     : https://prove2.me/theorems/63e6c060-cd7f-48d1-bc97-d432016b7b8b
-- title:
--   OAI.SharpPlanar.CachedData.ha9_0_8_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.ha9_0_8_contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma ha9_0_8_contains_g (j : Fin 7) : (ha9_0_8 j).Contains (fullFactor false 9 8 ((j.val:ℝ)/6))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.fullFactor` (definitions bundle `OAIQ098G1680` of this split); `OAI.SharpPlanar.CachedData.ha9_0_8` (definitions bundle `OAIQ098G406` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.hm9_1_0_8.realContains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders9.lean (declaration OAI.SharpPlanar.CachedData.ha9_0_8_contains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G406
import Definitions.Def_OAIQ098G1680

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma ha9_0_8_contains_g (j : Fin 7) : (ha9_0_8 j).Contains (fullFactor false 9 8 ((j.val:ℝ)/6)) := by
  sorry
end SharpPlanar.CachedData

end OAI
end
