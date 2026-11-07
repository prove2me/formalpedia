-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Numerical_U21_wuminus_column_e
-- name    : OAI.SharpPlanar.Numerical.U21.wuminus_column_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T21:53:28.990209+00:00
-- url     : https://prove2.me/theorems/565ce3f6-1b54-4d55-be5d-bde472fd4f64
-- title:
--   OAI.SharpPlanar.Numerical.U21.wuminus_column_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Numerical.U21.wuminus_column` of [lean/OAI/Analysis/PlanarPacking/Certificate/WUCert21.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert21.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.Numerical.U21`, with `open IntegerIntervals IntegerBasis IntegerGrid CachedData`):
--
--   ```lean
--   lemma wuminus_column_e (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Numerical.Wminus` (definitions bundle `OAIQ098E004` of this split); `OAI.SharpPlanar.Numerical.U21.umat` (definitions bundle `OAIQ098E126` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.Numerical.signedVU_norm_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert21.lean (declaration OAI.SharpPlanar.Numerical.U21.wuminus_column)

import Mathlib
import Definitions.Def_OAIQ098E126

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.Numerical.U21
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma wuminus_column_e (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  sorry
end SharpPlanar.Numerical.U21

end OAI
end
