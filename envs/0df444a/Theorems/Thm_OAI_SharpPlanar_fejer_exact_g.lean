-- Prove2me | Theorems.Thm_OAI_SharpPlanar_fejer_exact_g
-- name    : OAI.SharpPlanar.fejer_exact_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:17:30.253196+00:00
-- url     : https://prove2.me/theorems/86e617e4-9cfc-4458-82a6-a26617d54ab3
-- title:
--   OAI.SharpPlanar.fejer_exact_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.fejer_exact` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`):
--
--   ```lean
--   lemma fejer_exact_g (P : ℝ[X]) (hP : P.degree < 256) :
--       ∑ v ∈ Finset.range 256, fejerWeight v * P.eval (fejerNode v) =
--         (1/2:ℝ)*(∫ x in (-1:ℝ)..1, P.eval x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.fejerNode` and `OAI.SharpPlanar.fejerWeight` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.fejer_analytic_average_error_g` and `OAI.SharpPlanar.fejer_exact_monomial_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.fejer_exact)

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

namespace SharpPlanar

lemma fejer_exact_g (P : ℝ[X]) (hP : P.degree < 256) :
    ∑ v ∈ Finset.range 256, fejerWeight v * P.eval (fejerNode v) =
      (1/2:ℝ)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  sorry

end SharpPlanar

open MeasureTheory Set
open scoped BigOperators

end OAI
end
