-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_pareto_usualOrder_cond_of_failureRate_le
-- name    : LariviereIGFR.Moments.pareto_usualOrder_cond_of_failureRate_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:06.279374+00:00
-- url     : https://prove2.me/theorems/8b44593f-6471-47e1-8053-ed8c57b4b5c3
-- title:
--   Proof of Theorem 2, p. 603 — h(ξ) ≤ c/ξ for ξ > z ⇒ Pareto(z, c) is stochastically smaller than X_z
-- statement:
--   Let $X\ge 0$ have law $\mu$ with regular density $\phi$ and failure rate $h$. Let $z>0$ and $c>0$, with $\bar\Phi(z)>0$, and suppose
--   $$
--   h(\xi)\le\frac{c}{\xi}\qquad\text{for every }\xi>z .
--   $$
--   Then a Pareto random variable $P$ with parameters $(z,c)$ is stochastically smaller than $X_z$, the random variable $X$ conditional on $X>z$:
--   $$
--   \mathbb P(P>x)\le\mathbb P(X_z>x)\qquad\text{for all }x\in\mathbb R .
--   $$
--
--   In the paper $c=\kappa+\varepsilon$ with $0<\varepsilon<n-\kappa$; since the Pareto's $n$-th moment is then infinite, so is that of $X_z$ and hence of $X$.
--
--   **Formalization Note** The constant is any $c>0$ and the bound on $h$ is non-strict, so the same statement also yields the boundary case $n=\kappa$ of Theorem 2 (take $c=\kappa$), which the printed proof does not treat. "Stochastically smaller" is the published `StochasticOrders.Usual.UsualOrder`, here with the Pareto law first.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, proof of Theorem 2, second paragraph

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 2, p. 603: if `h(ξ) ≤ c/ξ` for every `ξ > z`, then the Pareto law with
parameters `(z, c)` is stochastically smaller than `X_z` (`X` conditional on `X > z`). The paper
uses `c = κ + ε`. -/
theorem pareto_usualOrder_cond_of_failureRate_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ)
    (z c : ℝ) (hz : 0 < z) (hc : 0 < c) (hsz : 0 < LariviereIGFR.Char.survival μ z)
    (hh : ∀ ξ, z < ξ → LariviereIGFR.Char.failureRate μ φ ξ ≤ c / ξ) :
    StochasticOrders.Usual.UsualOrder (paretoMeasure z c) (μ[|Set.Ioi z]) id id := by sorry

end LariviereIGFR.Moments
