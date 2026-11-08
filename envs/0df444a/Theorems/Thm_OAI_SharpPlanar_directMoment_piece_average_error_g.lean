-- Prove2me | Theorems.Thm_OAI_SharpPlanar_directMoment_piece_average_error_g
-- name    : OAI.SharpPlanar.directMoment_piece_average_error_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:13:52.916743+00:00
-- url     : https://prove2.me/theorems/bd4dc81b-e6ba-40bc-a739-163202055b76
-- title:
--   OAI.SharpPlanar.directMoment_piece_average_error_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.directMoment_piece_average_error` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma directMoment_piece_average_error_g (c d : ℕ → ℝ)
--       (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
--       {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
--       (hy : |y| ≤ 3/2) (ell : ℕ) :
--       ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, finiteDensity c d j (diskAffine j x) *
--           complexDirectFactor m y ell (diskAffine j x)) -
--         ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
--           (finiteDensity c d j (diskAffine j (fejerNode v.val)) *
--             complexDirectFactor m y ell (diskAffine j (fejerNode v.val)))‖ < 1/10^22
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.diskAffine`, `OAI.SharpPlanar.fejerNode`, `OAI.SharpPlanar.fejerWeight` and `OAI.SharpPlanar.finiteDensity` (definitions bundle `OAIQ098G072` of this split); `OAI.SharpPlanar.complexDirectFactor` (definitions bundle `OAIQ098G1643` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.directMoment_piece_error_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.directMoment_piece_average_error)

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1643

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

lemma directMoment_piece_average_error_g (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, finiteDensity c d j (diskAffine j x) *
        complexDirectFactor m y ell (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        (finiteDensity c d j (diskAffine j (fejerNode v.val)) *
          complexDirectFactor m y ell (diskAffine j (fejerNode v.val)))‖ < 1/10^22 := by
  sorry

end SharpPlanar

end OAI
end
