-- Prove2me | Theorems.Thm_OAI_SharpPlanar_IntegerBasis_u_norm_amplitude_g
-- name    : OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T04:24:56.914985+00:00
-- url     : https://prove2.me/theorems/00460d98-10e5-4228-afb1-fa049cd902b8
-- title:
--   OAI.SharpPlanar.IntegerBasis.u_norm_amplitude_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.IntegerBasis.u_norm_amplitude` of [lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar.IntegerBasis`, with `open scoped BigOperators ComplexConjugate ENNReal`, `open MeasureTheory`, `open IntegerIntervals IntegerAlpha`):
--
--   ```lean
--   lemma u_norm_amplitude_g (n j : ℕ) (t : ℝ) : ‖u n j t‖ = ‖uAmplitude n j t‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.u` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.IntegerBasis.uAmplitude` (definitions bundle `OAIQ098G322` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.IntegerBasis.basis_density_bounds_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean (declaration OAI.SharpPlanar.IntegerBasis.u_norm_amplitude)

import Mathlib
import Definitions.Def_OAIQ098G322

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma u_norm_amplitude_g (n j : ℕ) (t : ℝ) : ‖u n j t‖ = ‖uAmplitude n j t‖ := by
  sorry

end SharpPlanar.IntegerBasis

end OAI
end
