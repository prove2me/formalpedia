-- Prove2me | Theorems.Thm_OAI_SharpPlanar_complexLambda_differentiableAt_g
-- name    : OAI.SharpPlanar.complexLambda_differentiableAt_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:11:46.085817+00:00
-- url     : https://prove2.me/theorems/5a5b21ff-ffda-48a0-b11d-1f872f467375
-- title:
--   OAI.SharpPlanar.complexLambda_differentiableAt_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.complexLambda_differentiableAt` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma complexLambda_differentiableAt_g {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
--       DifferentiableAt ℂ complexLambda t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.h` (definitions bundle `OAIQ098G001` of this split); `OAI.SharpPlanar.complexLambda` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.complexTransformedFactor_differentiableAt_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.complexLambda_differentiableAt)

import Mathlib
import Definitions.Def_OAIQ098G072

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma complexLambda_differentiableAt_g {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexLambda t := by
  sorry

end SharpPlanar

end OAI
end
