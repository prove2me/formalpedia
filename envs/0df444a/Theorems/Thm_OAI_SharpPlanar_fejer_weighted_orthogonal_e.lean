-- Prove2me | Theorems.Thm_OAI_SharpPlanar_fejer_weighted_orthogonal_e
-- name    : OAI.SharpPlanar.fejer_weighted_orthogonal_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:57:54.163162+00:00
-- url     : https://prove2.me/theorems/a4c9c2f3-d4cd-4adf-bb88-29f8885d2bbd
-- title:
--   OAI.SharpPlanar.fejer_weighted_orthogonal_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.fejer_weighted_orthogonal` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`):
--
--   ```lean
--   lemma fejer_weighted_orthogonal_e (n : ℕ) :
--       (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
--         (∫ x, (T ℝ n).eval x ∂measureT) -
--         ∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
--           (∫ x, (T ℝ (2*a)).eval x*(T ℝ n).eval x ∂measureT)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerPolynomial` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.fejer_integral_even_e`, `OAI.SharpPlanar.fejer_integral_odd_e` and `OAI.SharpPlanar.fejer_integral_zero_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.fejer_weighted_orthogonal)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejer_weighted_orthogonal_e (n : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (∫ x, (T ℝ n).eval x ∂measureT) -
      ∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
        (∫ x, (T ℝ (2*a)).eval x*(T ℝ n).eval x ∂measureT) := by
  sorry

end SharpPlanar

open MeasureTheory Set
open scoped BigOperators

end OAI
end
