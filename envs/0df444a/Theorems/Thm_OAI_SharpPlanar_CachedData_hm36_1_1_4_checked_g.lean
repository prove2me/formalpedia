-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm36_1_1_4_checked_g
-- name    : OAI.SharpPlanar.CachedData.hm36_1_1_4.checked_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T22:01:19.462625+00:00
-- url     : https://prove2.me/theorems/ef6da141-7637-4426-8f83-911ad9d003c3
-- title:
--   OAI.SharpPlanar.CachedData.hm36_1_1_4.checked_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm36_1_1_4.checked` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm36_1_1_4`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma checked_g : cachedMomentRuleBox density1 hk36_1_4 = ans
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox` (definitions bundle `OAIQ098G079` of this split); `OAI.SharpPlanar.CachedData.hm36_1_1_4.ans` (definitions bundle `OAIQ098G1165` of this split); `OAI.SharpPlanar.CachedData.density1` (definitions bundle `OAIQ098G410` of this split); `OAI.SharpPlanar.CachedData.hk36_1_4` (definitions bundle `OAIQ098G619` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.CachedData.hm36_1_1_4.contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean (declaration OAI.SharpPlanar.CachedData.hm36_1_1_4.checked)

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G410
import Definitions.Def_OAIQ098G619
import Definitions.Def_OAIQ098G1165

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm36_1_1_4
lemma checked_g : cachedMomentRuleBox density1 hk36_1_4 = ans := by
  sorry
end hm36_1_1_4
end SharpPlanar.CachedData

end OAI
end
