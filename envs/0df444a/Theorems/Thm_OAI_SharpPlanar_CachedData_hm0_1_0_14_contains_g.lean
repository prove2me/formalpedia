-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm0_1_0_14_contains_g
-- name    : OAI.SharpPlanar.CachedData.hm0_1_0_14.contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T09:21:38.573915+00:00
-- url     : https://prove2.me/theorems/c59b7bea-8ec4-429d-b59a-c75a7f86742c
-- title:
--   OAI.SharpPlanar.CachedData.hm0_1_0_14.contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm0_1_0_14.contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm0_1_0_14`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma contains_g : ans.Contains (fullMomentRule true false 0 14)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.fullMomentRule` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.CachedData.hm0_1_0_14.ans` (definitions bundle `OAIQ098G769` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Bernstein0.N1_right.t14_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_1.lean (declaration OAI.SharpPlanar.CachedData.hm0_1_0_14.contains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G769
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm0_1_0_14
lemma contains_g : ans.Contains (fullMomentRule true false 0 14) := by
  sorry
end hm0_1_0_14
end SharpPlanar.CachedData

end OAI
end
