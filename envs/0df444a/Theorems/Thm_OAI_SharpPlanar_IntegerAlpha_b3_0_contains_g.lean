-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_0_contains_g
-- name    : OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T22:55:40.01742+00:00
-- url     : https://prove2.me/theorems/25d12868-a1d3-4e27-b7cc-a1ad33caa7ff
-- title:
--   OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerAlpha.b3_0_contains` of [lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerAlpha`, with `open IntegerIntervals IntegerBasis`):
--
--   ```lean
--   lemma b3_0_contains_g : b3_0.Contains (basisBeta 3 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerAlpha.b3_0` (definitions bundle `OAIQ098G017` of this split); `OAI.SharpPlanar.IntegerBasis.basisBeta` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerAlpha.bRow3_contains_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean (declaration OAI.SharpPlanar.IntegerAlpha.b3_0_contains)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma b3_0_contains_g : b3_0.Contains (basisBeta 3 0) := by
  sorry
end SharpPlanar.IntegerAlpha

end OAI
end
