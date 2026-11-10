-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm0_1_0_0_realContains_g
-- name    : OAI.SharpPlanar.CachedData.hm0_1_0_0.realContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T03:57:52.357259+00:00
-- url     : https://prove2.me/theorems/fb2a43ff-a80f-4d88-b29f-99fcd7192204
-- title:
--   OAI.SharpPlanar.CachedData.hm0_1_0_0.realContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm0_1_0_0.realContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm0_1_0_0`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma realContains_g : realAnswer.Contains (fullMoment true false 0 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.fullMoment` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.CachedData.hm0_1_0_0.realAnswer` (definitions bundle `OAIQ098G393` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.exactLeft_origin_positive_g` and `OAI.SharpPlanar.halfSign_0_N1_right_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_0.lean (declaration OAI.SharpPlanar.CachedData.hm0_1_0_0.realContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G393
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm0_1_0_0
lemma realContains_g : realAnswer.Contains (fullMoment true false 0 0) := by
  sorry
end hm0_1_0_0
end SharpPlanar.CachedData

end OAI
end
