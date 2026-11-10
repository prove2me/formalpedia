-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm15_1_1_3_realContains_g
-- name    : OAI.SharpPlanar.CachedData.hm15_1_1_3.realContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T04:12:18.326336+00:00
-- url     : https://prove2.me/theorems/9be2ee28-fa86-4699-92a1-042686a35f99
-- title:
--   OAI.SharpPlanar.CachedData.hm15_1_1_3.realContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm15_1_1_3.realContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock15_10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock15_10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm15_1_1_3`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma realContains_g : realAnswer.Contains (fullMoment true true 15 3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.fullMoment` (definitions bundle `OAIQ098G1682` of this split); `OAI.SharpPlanar.CachedData.hm15_1_1_3.realAnswer` (definitions bundle `OAIQ098G862` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein15.N0_left.t1_contains_g` and `OAI.SharpPlanar.Bernstein15.N0_right.t1_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock15_10.lean (declaration OAI.SharpPlanar.CachedData.hm15_1_1_3.realContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G862
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm15_1_1_3
lemma realContains_g : realAnswer.Contains (fullMoment true true 15 3) := by
  sorry
end hm15_1_1_3
end SharpPlanar.CachedData

end OAI
end
