-- Prove2me | Theorems.Thm_HighDimStat_TailBounds_lipschitz_gaussian_concentration
-- name    : HighDimStat.TailBounds.lipschitz_gaussian_concentration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:22:11.430985+00:00
-- url     : https://prove2.me/theorems/422b595b-8a74-4cb9-add6-0fad1d0b7f89
-- title:
--   Theorem 2.26 -- Gaussian concentration of Lipschitz functions
-- statement:
--   **Theorem 2.26 (Gaussian concentration of Lipschitz functions).** Let $(X_1,\dots,X_n)$ be a
--   vector of i.i.d. standard Gaussian variables, and let $f:\mathbb R^n\to\mathbb R$ be
--   $L$-Lipschitz with respect to the Euclidean norm. Then the variable $f(X)-\mathbb E[f(X)]$ is
--   sub-Gaussian with parameter at most $L$, and hence
--
--   $$
--   \mathbb P[|f(X)-\mathbb E[f(X)]|\ge t] \;\le\; 2e^{-t^2/2L^2} \qquad \text{for all } t\ge 0.
--   $$
--
--   This is a genuinely dimension-free concentration result: any $L$-Lipschitz function of a
--   standard Gaussian random vector, regardless of the ambient dimension $n$, concentrates like a
--   single scalar Gaussian variable of variance $L^2$.
--
--   **Formalization Note** "$X\sim N(0,I_n)$" is realized identically to Lemma 2.27's `X`
--   (`HasGaussianLaw` plus coordinatewise mean-zero and identity-covariance hypotheses). The
--   conclusion is stated as the conjunction of both parts of the book's own sentence — the
--   sub-Gaussian membership claim and its tail-bound corollary — rather than dropping the first as
--   redundant with the second, since the book states both explicitly.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 40 (PDF p. 60), Theorem 2.26, Eq. (2.39)

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
import Definitions.Def_HighDimStat_TailBounds_IsLLipschitz

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

/-- **Theorem 2.26** (Gaussian concentration of Lipschitz functions), Wainwright,
*High-Dimensional Statistics* (2019), p. 40. Let `(X1,...,Xn)` be a vector of i.i.d. standard
Gaussian variables, and let `f : ℝ^n → ℝ` be `L`-Lipschitz with respect to the Euclidean norm.
Then `f(X) - E[f(X)]` is sub-Gaussian with parameter at most `L`, and hence
`P[|f(X)-E[f(X)]| ≥ t] ≤ 2e^{-t²/2L²}` for all `t ≥ 0`. -/
theorem lipschitz_gaussian_concentration {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (X : Ω → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hXGauss : HasGaussianLaw X Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0)
    (hXcov : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0)
    (hLip : IsLLipschitz f L) :
    IsSubGaussian (fun ω => f (X ω) - ∫ ω', f (X ω') ∂Prob) Prob L ∧
    ∀ t : ℝ, 0 ≤ t →
      Prob.real {ω | t ≤ |f (X ω) - ∫ ω', f (X ω') ∂Prob|} ≤ 2 * Real.exp (-(t ^ 2) / (2 * L ^ 2))
    := by sorry

end HighDimStat.TailBounds
