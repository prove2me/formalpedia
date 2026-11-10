-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_exterior_exterior_norm_g
-- name    : OAI.SharpPlanar.Numerical.exterior_exterior_norm_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T12:17:05.925763+00:00
-- url     : https://prove2.me/theorems/6bd68a51-87b7-4b70-8a7d-f443afe29f81
-- title:
--   OAI.SharpPlanar.Numerical.exterior_exterior_norm_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.exterior_exterior_norm` of [lean/OAI/Analysis/PlanarPacking/FiniteTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma exterior_exterior_norm_g : ‖RE.comp (S.comp IE)‖ ≤ (28:ℝ)/100
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.X` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.L1Finite` and `OAI.SharpPlanar.S` (definitions bundle `OAIQ098G004` of this split); `OAI.SharpPlanar.Numerical.RE` (definitions bundle `OAIQ098G192` of this split); `OAI.SharpPlanar.Numerical.IE` (definitions bundle `OAIQ098G214` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.finiteA_bijective_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteTail.lean (declaration OAI.SharpPlanar.Numerical.exterior_exterior_norm)

import Mathlib
import Definitions.Def_OAIQ098G192
import Definitions.Def_OAIQ098G214

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical
open scoped BigOperators
lemma exterior_exterior_norm_g : ‖RE.comp (S.comp IE)‖ ≤ (28:ℝ)/100 := by
  sorry
end SharpPlanar.Numerical

end OAI
end
