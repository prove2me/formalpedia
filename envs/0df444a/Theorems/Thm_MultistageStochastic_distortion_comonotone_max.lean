-- Prove2me | Theorems.Thm_MultistageStochastic_distortion_comonotone_max
-- name    : MultistageStochastic.distortion_comonotone_max
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-23T20:24:51.402724+00:00
-- url     : https://prove2.me/theorems/3ad3ce67-60be-4563-8ba9-adfb86f25c31
-- title:
--   Corollary 3.19 — R_σ(Y) is the maximum of E(Y·σ(U)) over uniform U, attained by a co-monotone coupling
-- statement:
--   Let $\sigma$ be a distortion function and $Y\in L^\infty$ on an atomless probability space. Then
--   for every random variable $U$ that is uniformly distributed on $[0,1]$ under $P$,
--
--   $$
--   \mathbb E\bigl(Y\cdot\sigma(U)\bigr)\;\le\;\mathcal R_\sigma(Y),
--   $$
--
--   there is a uniformly distributed $U$ for which equality holds, and equality holds for **every**
--   uniform $U$ coupled with $Y$ in a co-monotone way, i.e. with
--   $P(Y\le y,\,U\le z)=\min\{P(Y\le y),P(U\le z)\}$ for all $y,z$ (the source's footnote 5):
--
--   $$
--   \mathcal R_\sigma(Y)\;=\;\max\bigl\{\mathbb E(Y\cdot\sigma(U)) : U\text{ uniformly }[0,1]\text{ distributed}\bigr\} .
--   \tag{3.20}
--   $$
--
--   This is Corollary 3.19, obtained from the dual representation by observing that $\sigma(U)$ is
--   feasible for (3.15) — its quantile function is $\sigma$ itself — and that the maximum is
--   attained when $Y$ and $U$ are coupled co-monotonically, that is, when $Y=G_Y^{-1}(U)$ almost
--   surely. It is the form in which distortion functionals are evaluated on scenario models.
--
--   **Formalization Note** The maximum is stated as its two halves, an upper bound for every
--   uniform $U$ and attainment by some uniform $U$, which is what "max" asserts; the corollary's
--   second sentence, "the maximum is attained whenever $Y$ and $U$ are coupled in a co-monotone
--   way", is the third conjunct, with co-monotonicity as defined in footnote 5. The atomless
--   hypothesis (mission II's splitting form) is added because a uniformly distributed $U$ exists on
--   $(\Omega,\mathcal F,P)$ only when the space carries no atoms; on a finite space the family is
--   empty and the source's maximum would not exist. The source states the corollary in the setting
--   of Section 3.3, which assumes such a space. Uniformity is $P(U\le u)=u$ on $[0,1]$; the integrand
--   $Y\cdot\sigma(U)$ is integrable for every uniform $U$ since $\sigma\in L^1(0,1)$ and $Y$ is bounded.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.3.2, printed p. 108 (PDF p. 121), Corollary 3.19: "The distortion risk functional R_σ(·) has the representation R_σ(Y) = max{E(Y · σ(U)) : U is uniformly [0, 1] distributed}. (3.20) The maximum is attained whenever Y and U are coupled in a co-monotone way."

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic
theorem distortion_comonotone_max {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hatom : Atomless P)
    (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ) (Y : Ω → ℝ) (hY : MemLinfty P Y) :
    (∀ U : Ω → ℝ, IsUniform P U →
        ∫ ω, Y ω * σ (U ω) ∂P ≤ distortionFunctional P σ Y) ∧
      (∃ U : Ω → ℝ, IsUniform P U ∧
        ∫ ω, Y ω * σ (U ω) ∂P = distortionFunctional P σ Y) ∧
      ∀ U : Ω → ℝ, IsUniform P U →
        (∀ y z : ℝ, P {ω | Y ω ≤ y ∧ U ω ≤ z} = min (P {ω | Y ω ≤ y}) (P {ω | U ω ≤ z})) →
        ∫ ω, Y ω * σ (U ω) ∂P = distortionFunctional P σ Y := by sorry
end MultistageStochastic
