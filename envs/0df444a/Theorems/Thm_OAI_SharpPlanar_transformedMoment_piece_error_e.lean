-- Prove2me | Theorems.Thm_OAI_SharpPlanar_transformedMoment_piece_error_e
-- name    : OAI.SharpPlanar.transformedMoment_piece_error_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:59:37.577882+00:00
-- url     : https://prove2.me/theorems/ad25564f-6bc2-4b24-a4ad-efb6240bb0f8
-- title:
--   OAI.SharpPlanar.transformedMoment_piece_error_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.transformedMoment_piece_error` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`, `open MeasureTheory`):
--
--   ```lean
--   lemma transformedMoment_piece_error_e (c d : ℕ → ℝ)
--       (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
--       {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
--       (hy : |y| ≤ 3/2) (ell : ℕ) :
--       ‖pieceIntegral (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j-
--         pieceRule (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ <
--           (1/10^22)/6
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.complexTransformedFactor`, `OAI.SharpPlanar.finiteDensity`, `OAI.SharpPlanar.pieceIntegral` and `OAI.SharpPlanar.pieceRule` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.transformedMoment_rule_error_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.transformedMoment_piece_error)

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

open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory

lemma transformedMoment_piece_error_e (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖pieceIntegral (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j-
      pieceRule (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ <
        (1/10^22)/6 := by
  sorry

end SharpPlanar

end OAI
end
