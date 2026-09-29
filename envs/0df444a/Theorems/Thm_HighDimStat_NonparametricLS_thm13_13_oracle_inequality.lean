-- Prove2me | Theorems.Thm_HighDimStat_NonparametricLS_thm13_13_oracle_inequality
-- name    : HighDimStat.NonparametricLS.thm13_13_oracle_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:30:47.682784+00:00
-- url     : https://prove2.me/theorems/d54dc1db-0065-49e6-9123-f5649a35b612
-- title:
--   An oracle inequality for nonparametric least squares (Theorem 13.13)
-- statement:
--   **Theorem 13.13** (p. 433), the goal of this mission. Let $\delta_n$ be any positive
--   solution of $G_n(\delta;\partial F)/\delta\le\delta/(2\sigma)$, where $\partial F=F-F$
--   (no longer requiring $f^*\in F$). There are universal positive constants
--   $(c_0,c_1,c_2)$ — not depending on the covariate space, sample size, function class,
--   $f^*$, $\sigma$, $\delta_n$ or $t$ — such that for any $t\ge\delta_n$, the nonparametric
--   least-squares estimate $\hat f_n$ satisfies, simultaneously for every $f\in F$,
--   $$
--   \|\hat f_n-f^*\|_n^2\le\inf_{\gamma\in(0,1)}\left[\frac{1+\gamma}{1-\gamma}\|f-f^*\|_n^2
--   +\frac{c_0}{\gamma(1-\gamma)}\,t\delta_n\right],
--   $$
--   with probability at least $1-c_1e^{-c_2nt\delta_n/\sigma^2}$.
--
--   This is called an oracle inequality because $\inf_{f\in F}\|f-f^*\|_n^2$ — attained at
--   $t=\delta_n$ by optimizing the right-hand side over $f$ — is the error that would be
--   achievable only by an oracle with direct access to uncorrupted samples of $f^*$; the bound
--   shows the least-squares estimate pays only a constant-factor penalty on this error, plus
--   the estimation-error term $\delta_n^2$. Setting $f=f^*$ (when $f^*\in F$) recovers
--   Theorem 13.5 up to constants.
--
--   **Formalization Note** The universal quantification over $(c_0,c_1,c_2)$ is placed
--   *before* the quantification over the covariate type, sample size, function class and all
--   other instance data, so the constants cannot secretly depend on the problem instance. The
--   infimum over $\gamma\in(0,1)$ is a real infimum over the (nonempty, e.g. $\gamma=1/2$)
--   subtype `{r : ℝ // r ∈ Set.Ioo 0 1}`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 433 (PDF p. 453), Theorem 13.13, Eq. (13.42)

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- **Theorem 13.13** (p. 433, PDF 453), the goal of this mission: an oracle inequality for
nonparametric least squares. Let `δn` be any positive solution of `Gₙ(δ; ∂F)/δ ≤ δ/(2σ)`
(Eq. (13.42a), with `∂F = F − F`, no longer requiring `f* ∈ F`). There are **universal**
positive constants `(c0, c1, c2)` — independent of `X`, `n`, `F`, `f*`, `σ`, `δn`, `t` — such
that for any `t ≥ δn`, the least-squares estimate `f̂ₙ` satisfies, simultaneously for every
`f ∈ F`,

`‖f̂ₙ − f*‖ₙ² ≤ inf_{γ∈(0,1)} [ (1+γ)/(1−γ) · ‖f − f*‖ₙ² + c0/(γ(1−γ)) · tδn ]`,

with probability at least `1 − c1 exp(−c2 n t δn / σ²)` (Eq. (13.42b)). -/
theorem thm13_13_oracle_inequality :
    ∃ c0 c1 c2 : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < c2 ∧
      ∀ {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}, 0 < n →
      ∀ (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P],
        IsIIDStdGaussian P w →
      ∀ (F : Set (X → ℝ)) (fStar : X → ℝ), IsStarShaped (diffClass F) →
      ∀ (σ : ℝ), 0 < σ →
      ∀ (y : Ω → Fin n → ℝ), (∀ ω i, y ω i = fStar (x i) + σ * w i ω) →
      ∀ (fHat : Ω → (X → ℝ)), (∀ ω, IsLeastSquaresEstimate x F (y ω) (fHat ω)) →
      ∀ (δn t : ℝ), SatisfiesCriticalInequality x w P (diffClass F) σ δn → δn ≤ t →
        1 - c1 * Real.exp (-c2 * ↑n * t * δn / σ ^ 2) ≤
          P.real {ω | ∀ f ∈ F, empiricalNormSq x (fun z => fHat ω z - fStar z) ≤
              ⨅ γ : {r : ℝ // r ∈ Set.Ioo (0 : ℝ) 1},
                (1 + γ.1) / (1 - γ.1) * empiricalNormSq x (fun z => f z - fStar z)
                  + c0 / (γ.1 * (1 - γ.1)) * t * δn} := by sorry

end HighDimStat.NonparametricLS
