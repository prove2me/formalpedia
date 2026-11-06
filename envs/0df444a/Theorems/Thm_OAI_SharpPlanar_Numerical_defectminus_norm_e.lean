-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_norm_e
-- name    : OAI.SharpPlanar.Numerical.defectminus_norm_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T21:05:07.736792+00:00
-- url     : https://prove2.me/theorems/88f6bdf9-8d5e-403f-9cef-963cb6be00c1
-- title:
--   OAI.SharpPlanar.Numerical.defectminus_norm_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.defectminus_norm` of [lean/OAI/Analysis/PlanarPacking/FiniteInverse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteInverse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical`):
--
--   ```lean
--   lemma defectminus_norm_e : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.L1Finite`, `OAI.SharpPlanar.matrixL1`, `OAI.SharpPlanar.Numerical.Aminus` and `OAI.SharpPlanar.Numerical.Wminus` (definitions bundle `OAIQ098E004` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Numerical.centralV_norm_e`, `OAI.SharpPlanar.Numerical.defectminus_lt_one_e` and `OAI.SharpPlanar.Numerical.signedVU_norm_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteInverse.lean (declaration OAI.SharpPlanar.Numerical.defectminus_norm)

import Mathlib
import Definitions.Def_OAIQ098E004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical
lemma defectminus_norm_e : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000 := by
  sorry
end SharpPlanar.Numerical

end OAI
end
