-- Prove2me | Theorems.Thm_OAI_SharpPlanar_cheb_integral_g
-- name    : OAI.SharpPlanar.cheb_integral_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T16:20:50.066694+00:00
-- url     : https://prove2.me/theorems/59b16339-9a9f-4dbd-80ad-25a91b44f3b3
-- title:
--   OAI.SharpPlanar.cheb_integral_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.cheb_integral` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`):
--
--   ```lean
--   lemma cheb_integral_g (n : ℕ) :
--       (∫ x in (-1:ℝ)..1, (T ℝ n).eval x) =
--       (1+(-1:ℝ)^n)/(1-(n:ℝ)^2)
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.fejer_cheb_integral_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.cheb_integral)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma cheb_integral_g (n : ℕ) :
    (∫ x in (-1:ℝ)..1, (T ℝ n).eval x) =
    (1+(-1:ℝ)^n)/(1-(n:ℝ)^2) := by
  sorry

end SharpPlanar

open MeasureTheory Set
open scoped BigOperators

end OAI
end
