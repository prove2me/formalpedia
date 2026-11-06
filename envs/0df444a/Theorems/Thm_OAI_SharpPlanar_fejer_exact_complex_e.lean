-- Prove2me | Theorems.Thm_OAI_SharpPlanar_fejer_exact_complex_e
-- name    : OAI.SharpPlanar.fejer_exact_complex_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:56:59.331991+00:00
-- url     : https://prove2.me/theorems/6adbb727-4ce6-404e-837a-4b7d0fbd439e
-- title:
--   OAI.SharpPlanar.fejer_exact_complex_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.fejer_exact_complex` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`):
--
--   ```lean
--   lemma fejer_exact_complex_e (c : ℕ → ℂ) :
--       (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*
--         (∑ k ∈ Finset.range 256, c k*(fejerNode v : ℂ)^k)) =
--         (1/2:ℂ)*(∫ x in (-1:ℝ)..1, ∑ k ∈ Finset.range 256, c k*(x:ℂ)^k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerNode` and `OAI.SharpPlanar.fejerWeight` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.fejer_analytic_average_error_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.fejer_exact_complex)

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

lemma fejer_exact_complex_e (c : ℕ → ℂ) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*
      (∑ k ∈ Finset.range 256, c k*(fejerNode v : ℂ)^k)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, ∑ k ∈ Finset.range 256, c k*(x:ℂ)^k) := by
  sorry

end SharpPlanar

open MeasureTheory Set
open scoped BigOperators

end OAI
end
