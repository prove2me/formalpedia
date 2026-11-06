-- Prove2me | Theorems.Thm_OAI_SharpPlanar_fejer_recip_sum_e
-- name    : OAI.SharpPlanar.fejer_recip_sum_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:42:38.1877+00:00
-- url     : https://prove2.me/theorems/3865375a-c8b5-45d2-b6a0-a64afa88fea6
-- title:
--   OAI.SharpPlanar.fejer_recip_sum_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.fejer_recip_sum` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`):
--
--   ```lean
--   lemma fejer_recip_sum_e (m : ℕ) :
--       (∑ a ∈ Finset.Icc 1 m, (2:ℝ)/(4*(a:ℝ)^2-1)) = 1-1/(2*(m:ℝ)+1)
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.fejerWeight_pos_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.fejer_recip_sum)

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

lemma fejer_recip_sum_e (m : ℕ) :
    (∑ a ∈ Finset.Icc 1 m, (2:ℝ)/(4*(a:ℝ)^2-1)) = 1-1/(2*(m:ℝ)+1) := by
  sorry

end SharpPlanar

open MeasureTheory Set
open scoped BigOperators

end OAI
end
