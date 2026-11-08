-- Prove2me | Theorems.Thm_OAI_SharpPlanar_analytic_taylor_error_g
-- name    : OAI.SharpPlanar.analytic_taylor_error_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T23:09:04.214054+00:00
-- url     : https://prove2.me/theorems/efb59e77-191f-416e-81a8-d07e0552c919
-- title:
--   OAI.SharpPlanar.analytic_taylor_error_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.analytic_taylor_error` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`):
--
--   ```lean
--   lemma analytic_taylor_error_g {f : ℂ → ℂ} {c z : ℂ} {R M r : ℝ}
--       (hR : 0 < R) (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr : r < 1)
--       (hf : DiffContOnCl ℂ f (Metric.ball c R))
--       (hbound : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
--       (hz : ‖z-c‖ ≤ r*R) (N : ℕ) :
--       ‖f z-taylorPolynomial f c N z‖ ≤ M*r^N/(1-r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.taylorPolynomial` (definitions bundle `OAIQ098G072` of this split).
--
--   **Used by.** The proof of `OAI.SharpPlanar.fejer_analytic_average_error_g` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.analytic_taylor_error)

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

lemma analytic_taylor_error_g {f : ℂ → ℂ} {c z : ℂ} {R M r : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr : r < 1)
    (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hbound : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
    (hz : ‖z-c‖ ≤ r*R) (N : ℕ) :
    ‖f z-taylorPolynomial f c N z‖ ≤ M*r^N/(1-r) := by
  sorry

end SharpPlanar

end OAI
end
