-- Prove2me | Theorems.Thm_OAI_SharpPlanar_CachedData_tm0_12_0_KContains_g
-- name    : OAI.SharpPlanar.CachedData.tm0_12_0.KContains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T03:09:14.333201+00:00
-- url     : https://prove2.me/theorems/dc71e27b-58be-4919-9847-a4c5e3e17a93
-- title:
--   OAI.SharpPlanar.CachedData.tm0_12_0.KContains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.CachedData.tm0_12_0.KContains` of [lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments12.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments12.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.CachedData.tm0_12_0`, with `open IntegerIntervals IntegerBasis IntegerGrid Numerical`):
--
--   ```lean
--   lemma KContains_g : realAnswer.Contains (tableMomentK false 12 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerIntervals.RBox.Contains` (definitions bundle `OAIQ098G083` of this split); `OAI.SharpPlanar.CachedData.tm0_12_0.realAnswer` (definitions bundle `OAIQ098G1456` of this split); `OAI.SharpPlanar.tableMomentK` (definitions bundle `OAIQ098G1682` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Residual12.bound1_1_g` and `OAI.SharpPlanar.residual_finite_exterior_1_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments12.lean (declaration OAI.SharpPlanar.CachedData.tm0_12_0.KContains)

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1456
import Definitions.Def_OAIQ098G1682

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_12_0
lemma KContains_g : realAnswer.Contains (tableMomentK false 12 0) := by
  sorry
end tm0_12_0

end SharpPlanar.CachedData

end OAI
end
