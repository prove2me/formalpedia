-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm19_1_0_6_realContains_g
-- name    : OAI.SharpPlanar.CachedData.hm19_1_0_6.realContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T04:18:14.308921+00:00
-- url     : https://prove2.me/theorems/d3b9ca3a-1e70-4500-aa51-6b61f5bd01d0
-- title:
--   OAI.SharpPlanar.CachedData.hm19_1_0_6.realContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm19_1_0_6.realContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock19_0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock19_0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm19_1_0_6`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma realContains_g : realAnswer.Contains (fullMoment true false 19 6)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.fullMoment` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.CachedData.hm19_1_0_6.realAnswer` (definitions bundle `OAIQ098G910` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein19.N1_left.bound_g` and `OAI.SharpPlanar.Bernstein19.N1_right.bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock19_0.lean (declaration OAI.SharpPlanar.CachedData.hm19_1_0_6.realContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G910
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm19_1_0_6
lemma realContains_g : realAnswer.Contains (fullMoment true false 19 6) := by
  sorry
end hm19_1_0_6
end SharpPlanar.CachedData

end OAI
end
