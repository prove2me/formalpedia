-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_gaussian_rotation_interpolation
-- name    : HighDimProb.RandomProcesses.gaussian_rotation_interpolation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T08:26:39.598523+00:00
-- url     : https://prove2.me/theorems/70929122-502a-4c4d-b5f1-45d487128055
-- title:
--   Gaussian interpolation in Hessian form
-- statement:
--   Let $G\in\mathbb R^{n+1}$ have independent standard normal coordinates, and let $L,M:\mathbb R^{n+1}\to E$ be continuous real-linear maps. Let $f:E\to\mathbb R$ be twice continuously differentiable, with $f$, $Df$ and $D^2f$ uniformly bounded. Set
--
--   $$Z_\theta=\cos\theta\,LG+\sin\theta\,MG,\qquad
--   U_i(\theta)=\cos\theta\,Le_i+\sin\theta\,Me_i,\qquad
--   V_i(\theta)=-\sin\theta\,Le_i+\cos\theta\,Me_i.$$
--
--   For every real $\theta$,
--
--   $$\frac{d}{d\theta}\mathbb E[f(Z_\theta)]=
--   \sum_{i=0}^{n}\mathbb E\big[D^2 f(Z_\theta)[U_i(\theta),V_i(\theta)]\big].$$
--
--   This Hessian form of Gaussian interpolation applies to singular linear images, allows correlated images, and is valid at the endpoints as well as in the interior. When $L$ and $M$ use disjoint coordinates, it specializes to independent Gaussian interpolation. The uniform bounds state explicitly the analytic hypotheses needed for differentiation under the expectation.
-- source:
--   Vershynin, High-Dimensional Probability (first edition), Lemma 7.2.7, equation (7.8), pp. 163–164 (PDF pp. 171–172). Hessian form for linear images, with the rotation parameter theta replacing the square-root parameter u. https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.gaussian_rotation_interpolation {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (∑ i : Fin (n + 1), ∫ x,
        (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)))
          (-Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) θ := by sorry
