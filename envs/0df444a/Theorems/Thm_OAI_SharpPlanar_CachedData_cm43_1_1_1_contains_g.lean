-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_cm43_1_1_1_contains_g
-- name    : OAI.SharpPlanar.CachedData.cm43_1_1_1.contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T08:22:43.641247+00:00
-- url     : https://prove2.me/theorems/660152f5-73c3-4e97-bc9d-3d860213405b
-- title:
--   OAI.SharpPlanar.CachedData.cm43_1_1_1.contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.cm43_1_1_1.contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/UMoments43.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments43.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.cm43_1_1_1`, with `open IntegerIntervals IntegerBasis IntegerGrid`):
--
--   ```lean
--   lemma contains_g : ans.Contains (momentRuleValue quadraturePoint fejerWeight 43 1 true true)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerWeight`, `OAI.SharpPlanar.IntegerBasis.momentRuleValue` and `OAI.SharpPlanar.IntegerGrid.quadraturePoint` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.cm43_1_1_1.ans` (definitions bundle `OAIQ098G164` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.U43.entry0_1_contains_g` and `OAI.SharpPlanar.Numerical.U43.entry3_1_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments43.lean (declaration OAI.SharpPlanar.CachedData.cm43_1_1_1.contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G164

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm43_1_1_1
lemma contains_g : ans.Contains (momentRuleValue quadraturePoint fejerWeight 43 1 true true) := by
  sorry
end cm43_1_1_1
end SharpPlanar.CachedData

end OAI
end
