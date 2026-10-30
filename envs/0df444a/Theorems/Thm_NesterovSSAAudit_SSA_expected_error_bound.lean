-- Prove2me | Theorems.Thm_NesterovSSAAudit_SSA_expected_error_bound
-- name    : NesterovSSAAudit.SSA.expected_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:23.951851+00:00
-- url     : https://prove2.me/theorems/1c4edea8-550c-43f5-a2a9-d05bd5ac07a3
-- title:
--   Theorem 7 — exact expected accuracy of stochastic simple averages
-- statement:
--   Let $E$ be a finite-dimensional real normed space with continuous dual $E^*$, and $Q\subseteq E$ nonempty closed and convex. Let $d$ be continuous on $Q$, strongly convex with parameter $\sigma>0$, and normalized at its minimizing prox-center $x_0$ by $d(x_0)=0$. Let $\pi_\beta(s)$ be the exact minimizer of $-\langle s,x\rangle+\beta d(x)$ on $Q$ for $\beta>0$. Let $\Xi$ be a sample carrier, $f:E\times\Xi\to\mathbb R$ the cost, $a:E\times\Xi\to E^*$ the oracle and $L\ge0$ their bound, satisfying the pointwise convexity, relative-subgradient and dual-norm-bound assumptions, and let $\gamma>0$. Starting with $s_0=0$ and the prox-center $x_0$, compute $g_i=a(x_i,\xi_i)$, $s_{i+1}=s_i+g_i$ and $x_{i+1}=\pi_{\gamma\hat\beta_{i+1}}(-s_{i+1})$. Write $\bar x_k=(k+1)^{-1}\sum_{i=0}^k x_i$, $F_D=\{x\in Q:d(x)\le D\}$, and $\delta_k(D)=\max_{x\in F_D}\sum_{i=0}^k\langle g_i,x_i-x\rangle$. The schedule is exactly $\hat\beta_0=\hat\beta_1=1$, $\hat\beta_{i+1}=\hat\beta_i+1/\hat\beta_i$ for $i\ge1$.
--
--   Let $\mu$ be a probability law on an arbitrary measurable sample space $\Xi$. Each feasible section $f(x,\cdot)$ is integrable. Define $\varphi(x)=\int f(x,\xi)\,d\mu(\xi)$ and take expectations over the law $\mu^{\otimes(k+1)}$ of fresh independent samples $\xi_0,\ldots,\xi_k$. The two canonical time-$n$ state maps are a.e. measurable on histories of length $n$ for every $n$. No measurability of the oracle away from the queried history states is assumed.
--
--   Let $x^*\in Q$ minimize $\varphi$ and set $\varphi^*=\varphi(x^*)$. For every integer $k\ge0$, the population cost of the arithmetic average is integrable and
--
--   $$\mathbb E[\varphi(\bar x_k)]-\varphi^*\le\frac{\hat\beta_{k+1}}{k+1}\left(\gamma d(x^*)+\frac{L^2}{2\sigma\gamma}\right).$$
--
--   This is Theorem 7 at its exact constant, for all admissible random executions. It leaves $\gamma>0$ arbitrary and permits unbounded or lower-dimensional $Q$, $L=0$ and nondifferentiable prox-functions. No pathwise deterministic-solution condition (2.8) is imposed on $x^*$.
--
--   Differences from the source:
--   - generalization: the source random cost variables and measurable canonical history states → an arbitrary measurable sample carrier, integrable fixed-input cost sections and a.e.-measurable canonical primal and dual history states; reason: finite-expectation source cost variables are integrable and source measurable states are a.e. measurable under each finite product law; Euclidean sample spaces and completed representatives are included
--   - encoding: functions defined on Q, dual pairings, and SSA paths → ambient extensions used only on Q, continuous-dual evaluation, and canonical finite-history recursion; reason: finite-dimensional duals are continuous; histories compute exactly (6.3), with unit weights and x0 through xk in every average
--   - encoding: well-defined finite expectations in the stochastic displays → fixed-input cost integrability as a source hypothesis and adaptive integrability as an explicit conclusion; reason: finite real expectations are integrable; making the adaptive conclusion explicit prevents total-integral defaults without imposing an extra oracle condition
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.27, Theorem 7

import Mathlib
import Definitions.Def_NesterovSSAAudit_SSA_randomExecution

set_option autoImplicit false

open Finset MeasureTheory PrimalDualSubgrad.Stoch

namespace NesterovSSAAudit.SSA

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace Ξ]

/-- September 2005 revised manuscript, p.27, Theorem 7, exact constant and all horizons.
The execution assumption concerns only the actual recursive history states. -/
theorem expected_error_bound
    (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E → Ξ → ℝ) (a : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : RawOracle Q f a L)
    (hsections : ∀ x ∈ Q, Integrable (f x) μ)
    (γ : ℝ) (hγ : 0 < γ) (hrandom : IsRandomExecution μ π γ x0 a)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, population μ f xstar ≤ population μ f x)
    (k : ℕ) :
    Integrable (fun h : Fin (k + 1) → Ξ =>
      population μ f (pathAverage π γ x0 a (padHistory h) k)) (historyLaw μ (k + 1)) ∧
    (∫ h : Fin (k + 1) → Ξ, population μ f (pathAverage π γ x0 a (padHistory h) k)
        ∂(historyLaw μ (k + 1))) - population μ f xstar
      ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by sorry

end NesterovSSAAudit.SSA
