-- Prove2me | Theorems.Thm_HighDimStat_NonparametricLS_thm13_5_basic_case_rate
-- name    : HighDimStat.NonparametricLS.thm13_5_basic_case_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:30:06.189354+00:00
-- url     : https://prove2.me/theorems/89361e2c-8930-445b-ac9f-568026242f86
-- title:
--   The basic-case rate for nonparametric least squares (Theorem 13.5)
-- statement:
--   **Theorem 13.5** (p. 423). Suppose the shifted function class $F^*=F-\{f^*\}$ is
--   star-shaped, and let $\delta_n$ be any positive solution of the critical inequality
--   $G_n(\delta;F^*)/\delta\le\delta/(2\sigma)$. Then for any $t\ge\delta_n$, the nonparametric
--   least-squares estimate $\hat f_n$, computed from data $y_i=f^*(x_i)+\sigma w_i$ with
--   $w_i\stackrel{iid}\sim N(0,1)$, satisfies
--   $$
--   \mathbb P\big[\|\hat f_n-f^*\|_n^2\ge 16\,t\delta_n\big]\le
--   e^{-nt\delta_n/(2\sigma^2)}.
--   $$
--
--   This is the special case $f^*\in F$ of the oracle inequality (Theorem 13.13): when the
--   true regression function actually lies in the class being fit, the least-squares estimate
--   concentrates around it at the rate set by the critical radius $\delta_n$.
--
--   **Formalization Note** `fHat : Ω → (X → ℝ)` is the (data-dependent) least-squares estimate:
--   for every noise realization `ω`, `fHat ω` minimizes the empirical squared error over `F`
--   on the data `y ω`. The probability is `P.real`, the `ℝ`-valued measure
--   (`ENNReal.toReal` of the outer measure), since `Measure` itself is `ℝ≥0∞`-valued.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 423 (PDF p. 443), Theorem 13.5, Eq. (13.20)

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- **Theorem 13.5** (p. 423, PDF 443). Suppose the shifted function class `F* = F − {f*}` is
star-shaped, and let `δn` be any positive solution of the critical inequality (13.17). Then
for any `t ≥ δn`, the nonparametric least-squares estimate `f̂ₙ`, computed from data
`yᵢ = f*(xᵢ) + σwᵢ` with `wᵢ` i.i.d. standard Gaussian, satisfies

`P[ ‖f̂ₙ − f*‖ₙ² ≥ 16 t δn ] ≤ exp( − n t δn / (2σ²) )`.

`fHat : Ω → (X → ℝ)` is the (data-dependent, hence random) least-squares estimate: for every
realization `ω` of the noise, `fHat ω` minimizes the empirical squared error over `F` on the
data `y ω`. -/
theorem thm13_5_basic_case_rate {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (hw : IsIIDStdGaussian P w)
    (F : Set (X → ℝ)) (fStar : X → ℝ) (hFstar : fStar ∈ F)
    (hStar : IsStarShaped (shiftedClass F fStar))
    (σ : ℝ) (hσ : 0 < σ)
    (y : Ω → Fin n → ℝ) (hy : ∀ ω i, y ω i = fStar (x i) + σ * w i ω)
    (fHat : Ω → (X → ℝ)) (hfHat : ∀ ω, IsLeastSquaresEstimate x F (y ω) (fHat ω))
    (δn t : ℝ) (hδn : SatisfiesCriticalInequality x w P (shiftedClass F fStar) σ δn)
    (ht : δn ≤ t) :
    P.real {ω | 16 * t * δn ≤ empiricalNormSq x (fun z => fHat ω z - fStar z)} ≤
      Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) := by sorry

end HighDimStat.NonparametricLS
