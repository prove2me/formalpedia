-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_gaussian_pi_integration_by_parts
-- name    : HighDimProb.RandomProcesses.gaussian_pi_integration_by_parts
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T07:59:35.715933+00:00
-- url     : https://prove2.me/theorems/101296ae-5192-40bc-9a6f-d57dfafdc621
-- title:
--   Coordinatewise Gaussian integration by parts
-- statement:
--   Let $G=(G_0,\ldots,G_n)$ have independent standard normal coordinates. Fix a coordinate $i$. Let $f,d_i f : \mathbb R^{n+1}\to\mathbb R$ satisfy that every section obtained by varying coordinate $i$ is differentiable, with derivative $d_i f$. Suppose $f(G)$, $d_i f(G)$ and $G_i f(G)$ are absolutely integrable. Then
--
--   $$\mathbb E[d_i f(G)]=\mathbb E[G_i f(G)].$$
--
--   This is the product-Gaussian form of multivariate integration by parts used to prove the covariance interpolation formula. It allows arbitrary finite dimension and imposes no independence assumptions on the function's arguments beyond the product Gaussian law.
-- source:
--   Vershynin, High-Dimensional Probability (first edition), Lemma 7.2.5 and Exercise 7.2.6, p. 163 (PDF p. 171). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. Explicit regularity and integrability hypotheses specify the analytic form used here.

import Mathlib
open MeasureTheory ProbabilityTheory Filter

theorem HighDimProb.RandomProcesses.gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ}
    (hderiv : ∀ (x : Fin (n + 1) → ℝ) (t : ℝ),
      HasDerivAt (fun y => f (Function.update x i y)) (df (Function.update x i t)) t)
    (hf : Integrable f (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hdf : Integrable df (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hxf : Integrable (fun x => x i * f x)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))) :
    (∫ x, df x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ x, x i * f x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by sorry
