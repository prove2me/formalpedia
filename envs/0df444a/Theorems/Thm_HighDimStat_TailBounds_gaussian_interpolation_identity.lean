-- Prove2me | Theorems.Thm_HighDimStat_TailBounds_gaussian_interpolation_identity
-- name    : HighDimStat.TailBounds.gaussian_interpolation_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:26.789309+00:00
-- url     : https://prove2.me/theorems/5201c8dd-5b85-4b01-bcc8-084ee5cc6e61
-- title:
--   Lemma 2.27 -- the Gaussian interpolation identity
-- statement:
--   **Lemma 2.27 (Gaussian interpolation identity).** Suppose that $f:\mathbb R^n\to\mathbb R$ is
--   differentiable. Then for any convex function $\varphi:\mathbb R\to\mathbb R$,
--
--   $$
--   \mathbb E\big[\varphi(f(X)-\mathbb E[f(X)])\big] \;\le\;
--   \mathbb E\Big[\varphi\Big(\frac{\pi}{2}\langle\nabla f(X), Y\rangle\Big)\Big],
--   $$
--
--   where $X, Y \sim N(0,I_n)$ are standard multivariate Gaussian and independent.
--
--   This is the classical interpolation identity, exploiting the rotation invariance of the
--   Gaussian distribution, that Theorem 2.26's proof builds on: applying it to $\varphi(t)=e^{\lambda t}$
--   converts a bound on $f(X)-\mathbb E[f(X)]$ into a bound on the (explicitly Gaussian, hence
--   directly computable) linear form $\langle\nabla f(X),Y\rangle$.
--
--   **Formalization Note** "$X,Y\sim N(0,I_n)$ independent" is realized via Mathlib's
--   `HasGaussianLaw` together with explicit coordinatewise mean-zero and identity-covariance
--   hypotheses (jointly pinning down the standard multivariate normal law) and `IndepFun`. The
--   inner product $\langle\nabla f(X),Y\rangle$ is realized as `fderiv ℝ f (X ω) (Y ω)` — the
--   Fréchet derivative of $f$ at $X(\omega)$ applied to $Y(\omega)$, which equals
--   $\langle\nabla f(X(\omega)),Y(\omega)\rangle$ by the Riesz representation of the gradient on
--   a Hilbert space, without needing to separately construct a gradient vector.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 41 (PDF p. 61), Lemma 2.27, Eq. (2.40)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

/-- **Lemma 2.27** (Gaussian interpolation identity), Wainwright, *High-Dimensional Statistics*
(2019), p. 41. If `f : ℝ^n → ℝ` is differentiable, then for any convex `φ : ℝ → ℝ`,
`E[φ(f(X)-E[f(X)])] ≤ E[φ((π/2)⟨∇f(X),Y⟩)]`, where `X, Y ~ N(0,Iₙ)` are standard multivariate
Gaussian and independent. -/
theorem gaussian_interpolation_identity {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (hXGauss : HasGaussianLaw X Prob) (hYGauss : HasGaussianLaw Y Prob)
    (hIndep : IndepFun X Y Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0) (hYmean : ∀ i, ∫ ω, Y ω i ∂Prob = 0)
    (hXcov : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0)
    (hYcov : ∀ i j, ∫ ω, Y ω i * Y ω j ∂Prob = if i = j then 1 else 0)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hInt1 : Integrable (fun ω => φ (f (X ω) - ∫ ω', f (X ω') ∂Prob)) Prob)
    (hInt2 : Integrable (fun ω => φ (Real.pi / 2 * fderiv ℝ f (X ω) (Y ω))) Prob) :
    ∫ ω, φ (f (X ω) - ∫ ω', f (X ω') ∂Prob) ∂Prob ≤
      ∫ ω, φ (Real.pi / 2 * fderiv ℝ f (X ω) (Y ω)) ∂Prob := by sorry

end HighDimStat.TailBounds
