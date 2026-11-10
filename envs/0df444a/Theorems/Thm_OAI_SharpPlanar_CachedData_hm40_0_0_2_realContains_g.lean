-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm40_0_0_2_realContains_g
-- name    : OAI.SharpPlanar.CachedData.hm40_0_0_2.realContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T04:58:22.035281+00:00
-- url     : https://prove2.me/theorems/8c7ec164-2742-4863-926a-9d1de7d171bf
-- title:
--   OAI.SharpPlanar.CachedData.hm40_0_0_2.realContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm40_0_0_2.realContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock40_0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock40_0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm40_0_0_2`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma realContains_g : realAnswer.Contains (fullMoment false false 40 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.hm40_0_0_2.realAnswer` (definitions bundle `OAIQ098G1256` of this split); `OAI.SharpPlanar.fullMoment` (definitions bundle `OAIQ098G1682` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein40.N0_left.t0_contains_g` and `OAI.SharpPlanar.Bernstein40.N0_right.t0_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock40_0.lean (declaration OAI.SharpPlanar.CachedData.hm40_0_0_2.realContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1256
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm40_0_0_2
lemma realContains_g : realAnswer.Contains (fullMoment false false 40 2) := by
  sorry
end hm40_0_0_2
end SharpPlanar.CachedData

end OAI
end
