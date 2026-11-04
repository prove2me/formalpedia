-- Prove2me | Theorems.Thm_OAI_SharpPlanar_positive_quadrature_error_e
-- name    : OAI.SharpPlanar.positive_quadrature_error_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T05:43:22.153813+00:00
-- url     : https://prove2.me/theorems/b2d59a93-1a62-43ef-a387-ecdef7df7233
-- title:
--   OAI.SharpPlanar.positive_quadrature_error_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.positive_quadrature_error` of [lean/OAI/Analysis/PlanarPacking/Quadrature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Real Polynomial Finset MeasureTheory`, `open Polynomial.Chebyshev`, `open MeasureTheory Set`, `open scoped BigOperators`):
--
--   ```lean
--   lemma positive_quadrature_error_e {ι : Type*} [Fintype ι]
--       (a b : ℝ) (hab : a ≤ b) (w t : ι → ℝ) (f p : ℝ → ℂ) (ε : ℝ)
--       (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, t i ∈ Icc a b)
--       (hmass : ∑ i, w i = b-a)
--       (hf : ContinuousOn f (Icc a b)) (hp : ContinuousOn p (Icc a b))
--       (herr : ∀ x ∈ Icc a b, ‖f x-p x‖ ≤ ε)
--       (hexact : (∫ x in a..b, p x) = ∑ i, (w i : ℂ)*p (t i)) :
--       ‖(∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i)‖ ≤ 2*(b-a)*ε
--   ```
--
--   **Used by.** The proof of `OAI.SharpPlanar.fejer_analytic_average_error_e` of this split imports it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Quadrature.lean (declaration OAI.SharpPlanar.positive_quadrature_error)

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

lemma positive_quadrature_error_e {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (w t : ι → ℝ) (f p : ℝ → ℂ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, t i ∈ Icc a b)
    (hmass : ∑ i, w i = b-a)
    (hf : ContinuousOn f (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (herr : ∀ x ∈ Icc a b, ‖f x-p x‖ ≤ ε)
    (hexact : (∫ x in a..b, p x) = ∑ i, (w i : ℂ)*p (t i)) :
    ‖(∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i)‖ ≤ 2*(b-a)*ε := by
  sorry

end SharpPlanar

end OAI
end
