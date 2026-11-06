-- Prove2me | Theorems.Thm_OAI_SharpPlanar_cheb_primitive_deriv_e
-- name    : OAI.SharpPlanar.cheb_primitive_deriv_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:42:15.639706+00:00
-- url     : https://prove2.me/theorems/dd68553f-8315-4348-b6b3-0cb0da0b24e9
-- title:
--   OAI.SharpPlanar.cheb_primitive_deriv_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.cheb_primitive_deriv` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`):
--
--   ```lean
--   lemma cheb_primitive_deriv_e (n : ℤ) (hn₁ : n+1 ≠ 0) (hn₂ : n-1 ≠ 0) (x : ℝ) :
--       HasDerivAt (fun x : ℝ => (T ℝ (n+1)).eval x/(2*(n+1:ℤ))-
--         (T ℝ (n-1)).eval x/(2*(n-1:ℤ))) ((T ℝ n).eval x) x
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.cheb_integral_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.cheb_primitive_deriv)

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

lemma cheb_primitive_deriv_e (n : ℤ) (hn₁ : n+1 ≠ 0) (hn₂ : n-1 ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (T ℝ (n+1)).eval x/(2*(n+1:ℤ))-
      (T ℝ (n-1)).eval x/(2*(n-1:ℤ))) ((T ℝ n).eval x) x := by
  sorry

end SharpPlanar

open MeasureTheory Set
open scoped BigOperators

end OAI
end
