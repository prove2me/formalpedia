-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_gaussian_linear_integration_by_parts
-- name    : HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T07:59:49.530376+00:00
-- url     : https://prove2.me/theorems/cdb78311-ed12-4e99-80ff-cb36e21e7f68
-- title:
--   Gaussian integration by parts after a linear transformation
-- statement:
--   Let $G=(G_0,\ldots,G_n)$ have independent standard normal coordinates, let $L:\mathbb R^{n+1}\to E$ be a continuous real-linear map into a real normed space, and let $f:E\to\mathbb R$ be continuously differentiable. Suppose $f$ and the operator norm of its derivative are bounded. For the $i$th standard basis vector $e_i$,
--
--   $$\mathbb E[Df(LG)[Le_i]]=\mathbb E[G_i f(LG)].$$
--
--   This chain-rule form is useful for Gaussian vectors with arbitrary covariance, including singular covariance: the linear map need not be injective or surjective. It is a reusable input for Gaussian interpolation.
-- source:
--   Vershynin, High-Dimensional Probability (first edition), Lemma 7.2.5 and Exercise 7.2.6, p. 163 (PDF p. 171). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. Explicit regularity and integrability hypotheses specify the analytic form used here.

import Mathlib
open MeasureTheory ProbabilityTheory Filter

theorem HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (i : Fin (n + 1))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, fderiv ℝ f (L x) (L (Pi.single i 1))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ x, x i * f (L x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by sorry
