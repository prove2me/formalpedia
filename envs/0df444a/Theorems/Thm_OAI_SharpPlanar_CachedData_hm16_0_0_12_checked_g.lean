-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm16_0_0_12_checked_g
-- name    : OAI.SharpPlanar.CachedData.hm16_0_0_12.checked_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:01:55.276444+00:00
-- url     : https://prove2.me/theorems/42932968-58de-45e7-b046-d16b666343c7
-- title:
--   OAI.SharpPlanar.CachedData.hm16_0_0_12.checked_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm16_0_0_12.checked` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock16_1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock16_1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm16_0_0_12`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma checked_g : cachedMomentRuleBox density0 hk16_0_12 = ans
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox` (definitions bundle `OAIQ098G079` of this split); `OAI.SharpPlanar.CachedData.density0` (definitions bundle `OAIQ098G395` of this split); `OAI.SharpPlanar.CachedData.hk16_0_12` (definitions bundle `OAIQ098G515` of this split); `OAI.SharpPlanar.CachedData.hm16_0_0_12.ans` (definitions bundle `OAIQ098G862` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein16.N0_left.t10_contains_g` and `OAI.SharpPlanar.Bernstein16.N0_right.t10_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock16_1.lean (declaration OAI.SharpPlanar.CachedData.hm16_0_0_12.checked)

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G515
import Definitions.Def_OAIQ098G862

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm16_0_0_12
lemma checked_g : cachedMomentRuleBox density0 hk16_0_12 = ans := by
  sorry
end hm16_0_0_12
end SharpPlanar.CachedData

end OAI
end
