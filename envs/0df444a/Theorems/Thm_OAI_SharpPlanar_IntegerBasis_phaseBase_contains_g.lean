-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phaseBase_contains_g
-- name    : OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:31:27.895478+00:00
-- url     : https://prove2.me/theorems/89ac0f95-2d93-470d-acc7-96653b99e659
-- title:
--   OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerBasis.phaseBase_contains` of [lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerBasis`, with `open IntegerIntervals`):
--
--   ```lean
--   lemma phaseBase_contains_g : phaseBase.Contains (phase12 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.IntegerBasis.phase12` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.IntegerBasis.phaseBase` (definitions bundle `OAIQ098G075` of this split); `OAI.SharpPlanar.IntegerIntervals.CBox.Contains` (definitions bundle `OAIQ098G083` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerAlpha.a0_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a0_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a10_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a11_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a1_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a2_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a3_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a4_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a5_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a6_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a7_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a8_5_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_0_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_1_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_2_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_3_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_4_contains_g`, `OAI.SharpPlanar.IntegerAlpha.a9_5_contains_g` and `OAI.SharpPlanar.IntegerBasis.betaBox_contains_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean (declaration OAI.SharpPlanar.IntegerBasis.phaseBase_contains)

import Mathlib
import Definitions.Def_OAIQ098G075
import Definitions.Def_OAIQ098G083

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phaseBase_contains_g : phaseBase.Contains (phase12 1) := by
  sorry

end SharpPlanar.IntegerBasis

end OAI
end
