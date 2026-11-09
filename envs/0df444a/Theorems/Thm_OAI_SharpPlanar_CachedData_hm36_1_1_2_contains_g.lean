-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_hm36_1_1_2_contains_g
-- name    : OAI.SharpPlanar.CachedData.hm36_1_1_2.contains_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-08T23:21:20.01925+00:00
-- url     : https://prove2.me/theorems/498b4add-3788-4555-9554-00b6a881706c
-- title:
--   OAI.SharpPlanar.CachedData.hm36_1_1_2.contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.hm36_1_1_2.contains` of [lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.hm36_1_1_2`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma contains_g : ans.Contains (fullMomentRule true true 36 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.hm36_1_1_2.ans` (definitions bundle `OAIQ098G1165` of this split); `OAI.SharpPlanar.fullMomentRule` (definitions bundle `OAIQ098G1682` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Bernstein36.N0_left.t0_contains_g` and `OAI.SharpPlanar.Bernstein36.N0_right.t0_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean (declaration OAI.SharpPlanar.CachedData.hm36_1_1_2.contains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1165
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm36_1_1_2
lemma contains_g : ans.Contains (fullMomentRule true true 36 2) := by
  sorry
end hm36_1_1_2
end SharpPlanar.CachedData

end OAI
end
