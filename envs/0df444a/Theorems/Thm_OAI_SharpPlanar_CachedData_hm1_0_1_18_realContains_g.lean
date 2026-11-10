-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm1_0_1_18_realContains_g
-- name    : OAI.SharpPlanar.CachedData.hm1_0_1_18.realContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T04:24:09.981782+00:00
-- url     : https://prove2.me/theorems/040d02e5-47f8-48a0-8237-3f145c751d97
-- title:
--   OAI.SharpPlanar.CachedData.hm1_0_1_18.realContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm1_0_1_18.realContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments1_6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments1_6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm1_0_1_18`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma realContains_g : realAnswer.Contains (fullMoment false true 1 18)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.fullMoment` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.CachedData.hm1_0_1_18.realAnswer` (definitions bundle `OAIQ098G947` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein1.N1_left.bound_g` and `OAI.SharpPlanar.Bernstein1.N1_right.bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments1_6.lean (declaration OAI.SharpPlanar.CachedData.hm1_0_1_18.realContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G947
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm1_0_1_18
lemma realContains_g : realAnswer.Contains (fullMoment false true 1 18) := by
  sorry
end hm1_0_1_18
end SharpPlanar.CachedData

end OAI
end
