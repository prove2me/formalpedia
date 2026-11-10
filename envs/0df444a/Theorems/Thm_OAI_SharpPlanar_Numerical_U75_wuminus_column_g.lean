-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U75_wuminus_column_g
-- name    : OAI.SharpPlanar.Numerical.U75.wuminus_column_g
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-09T20:19:12.58474+00:00
-- url     : https://prove2.me/theorems/ca502533-690f-4f90-8689-22aa511be07b
-- title:
--   OAI.SharpPlanar.Numerical.U75.wuminus_column_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U75.wuminus_column` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert75.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert75.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U75`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma wuminus_column_g (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Numerical.Wminus` (definitions bundle `OAIQ098G004` of this split); `OAI.SharpPlanar.Numerical.U75.umat` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.signedVU_norm_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert75.lean (declaration OAI.SharpPlanar.Numerical.U75.wuminus_column)

import Mathlib
import Definitions.Def_OAIQ098G362

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U75
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma wuminus_column_g (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  sorry
end SharpPlanar.Numerical.U75

end OAI
end
