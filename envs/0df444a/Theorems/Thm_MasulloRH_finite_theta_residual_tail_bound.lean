-- Prove2me | Theorems.Thm_MasulloRH_finite_theta_residual_tail_bound
-- name    : MasulloRH.finite_theta_residual_tail_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:21:24.361516+00:00
-- url     : https://prove2.me/theorems/2d121368-d18c-484d-9ad7-8213e62d8b2d
-- title:
--   Explicit tail energy and integrability for arbitrary finite theta residuals
-- statement:
--   Let $m$ be a nonnegative integer, $T\ge0$, and $R\ge1/2$. Let $c,b\in\mathbb R$ satisfy $0<c-b$ and $c+b<1$. For arbitrary complex coefficients $a_i$ and real shifts $y_i$ with $|y_i-\log2|\le R$, use the mission's canonical functions
--
--   $$p_T(x)=\frac{T+1}{\sqrt\pi}e^{-(T+1)^2x^2},\qquad r(x)=p_T(x)-\sum_{i<m}a_i\theta(x-y_i).$$
--
--   Write
--
--   $$w(x)=e^{2cx+2b|x|},\qquad E(r)=\int_{\mathbb R}w(x)|r(x)|^2\,dx,\qquad E_R(r)=\int_{-R}^{R}w(x)|r(x)|^2\,dx.$$
--
--   Define explicit endpoint amplitudes
--
--   $$A=\frac{T+1}{\sqrt\pi}e^{-(T+1)^2R^2},$$
--
--   $$C=A+\sum_{i<m}|a_i|\,24e^{-\pi e^{2(R-y_i)}},$$
--
--   $$D=A+\sum_{i<m}|a_i|\,12e^{R+y_i-(\pi/16)e^{2(R+y_i)}}.$$
--
--   Then $x\mapsto w(x)|r(x)|^2$ is Lebesgue integrable, and
--
--   $$0\le E(r)-E_R(r)\le\frac{C^2e^{2(c+b)R}}{2-2(c+b)}+\frac{D^2e^{-2(c-b)R}}{2(c-b)}.$$
--
--   Both denominators are strictly positive under the displayed strip conditions. The statement also covers the empty sum $m=0$. It concerns the actual theta function and the canonical Gaussian pulse; it places no smallness condition on the residual energy.
--
--   **Formalization Note.** Coefficients and shifts are indexed by `Fin m`, and `|a_i|` is the complex norm. The finite-interval integral is over `Set.Icc (-R) R` with Lebesgue measure. The formal expression `(Real.exp t)^2` equals the displayed $e^{2t}$. Integrability and the nonnegativity of the discarded energy are conclusions, rather than hypotheses.
-- source:
--   Original supporting estimate for the Prove2Me Masullo RH specialization mission, using its canonical GaussianThetaApproximation definition (6f34c003-4870-4c6a-b83e-256b289a15db). The formal proof uses the accepted theta reflection theorem https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe and Gaussian-series truncation bound https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 . This general residual estimate is contributed as reusable certification infrastructure; it is not attributed to a specific theorem or page in Masullo's manuscript.

import Definitions.Def_MasulloRH_GaussianThetaApproximation

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
open MasulloRH.GaussianApproximation

theorem MasulloRH.finite_theta_residual_tail_bound
    (m : ℕ) (T c b R : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hR : (1/2 : ℝ) ≤ R)
    (hleft : 0 < c-b) (hright : c+b < 1)
    (hshift : ∀ i : Fin m, |y i - Real.log 2| ≤ R) :
    let A : ℝ := ((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)
    let C : ℝ := A + ∑ i, ‖a i‖ *
      (24 * Real.exp (-Real.pi*(Real.exp (R-y i))^2))
    let D : ℝ := A + ∑ i, ‖a i‖ *
      (12 * Real.exp (R+y i-(Real.pi/16)*(Real.exp (R+y i))^2))
    Integrable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    0 ≤ energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ≤
      C^2 * Real.exp (2*(c+b)*R) / (2-2*(c+b)) +
      D^2 * Real.exp (-2*(c-b)*R) / (2*(c-b))  := by sorry
