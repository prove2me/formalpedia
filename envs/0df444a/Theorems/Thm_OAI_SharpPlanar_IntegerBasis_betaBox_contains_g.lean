-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerBasis_betaBox_contains_g
-- name    : OAI.SharpPlanar.IntegerBasis.betaBox_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T02:33:50.257105+00:00
-- url     : https://prove2.me/theorems/c87017ea-528c-420b-b6e3-6822d4418dad
-- title:
--   OAI.SharpPlanar.IntegerBasis.betaBox_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerBasis.betaBox_contains` of [lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerBasis`, with `open IntegerIntervals`):
--
--   ```lean
--   lemma betaBox_contains_g (n j : ℕ) : (betaBox n j).Contains (basisBeta n j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerBasis.basisBeta` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerBasis.betaBox` (definitions bundle `OAIQ098G080` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerAlpha.b0_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b0_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b10_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b11_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b1_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b2_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b3_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b4_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b5_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b6_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b7_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b8_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.b9_4_contains_g` and `OAI.SharpPlanar.IntegerAlpha.b9_5_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean (declaration OAI.SharpPlanar.IntegerBasis.betaBox_contains)

import Mathlib
import Definitions.Def_OAIQ098G080
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma betaBox_contains_g (n j : ℕ) : (betaBox n j).Contains (basisBeta n j) := by
  sorry

end SharpPlanar.IntegerBasis

end OAI
end
