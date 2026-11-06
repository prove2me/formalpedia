-- Prove2me | Theorems.Thm_OAI_SharpPlanar_geometric_tail_error_e
-- name    : OAI.SharpPlanar.geometric_tail_error_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:42:37.632575+00:00
-- url     : https://prove2.me/theorems/0cf93363-acfa-4da0-a1a8-9697ef3a6803
-- title:
--   OAI.SharpPlanar.geometric_tail_error_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.geometric_tail_error` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`):
--
--   ```lean
--   lemma geometric_tail_error_e {a : ℕ → ℂ} {v : ℂ} {M r : ℝ}
--       (ha : HasSum a v) (hr0 : 0 ≤ r) (hr : r < 1)
--       (hb : ∀ n, ‖a n‖ ≤ M*r^n) (N : ℕ) :
--       ‖v-∑ n ∈ Finset.range N, a n‖ ≤ M*r^N/(1-r)
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.analytic_taylor_error_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.geometric_tail_error)

import Mathlib

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

lemma geometric_tail_error_e {a : ℕ → ℂ} {v : ℂ} {M r : ℝ}
    (ha : HasSum a v) (hr0 : 0 ≤ r) (hr : r < 1)
    (hb : ∀ n, ‖a n‖ ≤ M*r^n) (N : ℕ) :
    ‖v-∑ n ∈ Finset.range N, a n‖ ≤ M*r^N/(1-r) := by
  sorry

end SharpPlanar

end OAI
end
