-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_cond_usualOrder_pareto_of_le_failureRate
-- name    : LariviereIGFR.Moments.cond_usualOrder_pareto_of_le_failureRate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:12.496773+00:00
-- url     : https://prove2.me/theorems/d3e78c1b-37f1-4786-9526-2f900ed5ab07
-- title:
--   Proof of Theorem 2, p. 603 — h(ξ) > c/ξ for ξ > y ⇒ X_y is stochastically smaller than Pareto(y, c)
-- statement:
--   Let $X\ge 0$ have law $\mu$ with regular density $\phi$ and failure rate $h$. Let $y>0$ and $c>0$, with $\bar\Phi(y)>0$, and suppose
--   $$
--   h(\xi)>\frac{c}{\xi}\qquad\text{for every }\xi>y\text{ with }\Phi(\xi)<1 .
--   $$
--   Then $X_y$, the random variable $X$ conditional on $X>y$, is stochastically smaller than a Pareto random variable $P$ with parameters $(y,c)$ (density $cy^c\xi^{-c-1}$ on $\xi\ge y$):
--   $$
--   \mathbb P(X_y>x)\le\mathbb P(P>x)\qquad\text{for all }x\in\mathbb R .
--   $$
--
--   In the paper $c=n+\varepsilon$ with $0<\varepsilon<\kappa-n$, and the comparison transfers the finite $n$-th moment of the Pareto to $X_y$.
--
--   **Formalization Note** "Stochastically smaller" is the published usual stochastic order `StochasticOrders.Usual.UsualOrder` applied to the two laws with the identity map. The constant $n+\varepsilon$ of the paper is abstracted to any $c>0$. Points where $\Phi(\xi)=1$ are exempted from the hypothesis because there the paper's failure rate is $+\infty$ while Lean's division gives $0$; with this exemption the statement also covers laws with bounded support, and it is at least as strong as the version without it.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, proof of Theorem 2, first paragraph

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 2, p. 603: if `h(ξ) > c/ξ` for every `ξ > y` (with `Φ(ξ) < 1`), then `X_y`
(`X` conditional on `X > y`) is stochastically smaller than the Pareto law with parameters `(y, c)`.
The paper uses `c = n + ε`. -/
theorem cond_usualOrder_pareto_of_le_failureRate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ)
    (y c : ℝ) (hy : 0 < y) (hc : 0 < c) (hsy : 0 < LariviereIGFR.Char.survival μ y)
    (hh : ∀ ξ, y < ξ → cdf μ ξ < 1 → c / ξ < LariviereIGFR.Char.failureRate μ φ ξ) :
    StochasticOrders.Usual.UsualOrder (μ[|Set.Ioi y]) (paretoMeasure y c) id id := by sorry

end LariviereIGFR.Moments
