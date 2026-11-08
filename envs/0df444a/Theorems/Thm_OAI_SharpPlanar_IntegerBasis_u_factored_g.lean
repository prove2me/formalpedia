-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerBasis_u_factored_g
-- name    : OAI.SharpPlanar.IntegerBasis.u_factored_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:04:49.660036+00:00
-- url     : https://prove2.me/theorems/70ea84ad-df65-4eae-9197-6106c7d3be11
-- title:
--   OAI.SharpPlanar.IntegerBasis.u_factored_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerBasis.u_factored` of [lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerBasis`, with `open IntegerIntervals`):
--
--   ```lean
--   lemma u_factored_g (n j : ℕ) (t : ℝ) : u n j t =
--       -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
--         (basisBeta n j-(t:ℂ)*basisAlpha n j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.u` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.IntegerBasis.basisAlpha` and `OAI.SharpPlanar.IntegerBasis.basisBeta` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.IntegerBasis.basisFunction_wave_g` and `OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean (declaration OAI.SharpPlanar.IntegerBasis.u_factored)

import Mathlib
import Definitions.Def_OAIQ098G072

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma u_factored_g (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  sorry

end SharpPlanar.IntegerBasis

end OAI
end
