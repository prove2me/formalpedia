-- Prove2me | Theorems.Thm_NesterovSSAAudit_SSA_expected_gap_lower_bound
-- name    : NesterovSSAAudit.SSA.expected_gap_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:44:05.771464+00:00
-- url     : https://prove2.me/theorems/cd3a2ba3-7a4e-4703-9160-82aa5e4d95cd
-- title:
--   §6, Eq. (6.6) — expected gap lower bound
-- statement:
--   Let $E$ be a finite-dimensional real normed space with continuous dual $E^*$, and $Q\subseteq E$ nonempty closed and convex. Let $d$ be continuous on $Q$, strongly convex with parameter $\sigma>0$, and normalized at its minimizing prox-center $x_0$ by $d(x_0)=0$. Let $\pi_\beta(s)$ be the exact minimizer of $-\langle s,x\rangle+\beta d(x)$ on $Q$ for $\beta>0$. Let $\Xi$ be a sample carrier, $f:E\times\Xi\to\mathbb R$ the cost, $a:E\times\Xi\to E^*$ the oracle and $L\ge0$ their bound, satisfying the pointwise convexity, relative-subgradient and dual-norm-bound assumptions, and let $\gamma>0$. Starting with $s_0=0$ and the prox-center $x_0$, compute $g_i=a(x_i,\xi_i)$, $s_{i+1}=s_i+g_i$ and $x_{i+1}=\pi_{\gamma\hat\beta_{i+1}}(-s_{i+1})$. Write $\bar x_k=(k+1)^{-1}\sum_{i=0}^k x_i$, $F_D=\{x\in Q:d(x)\le D\}$, and $\delta_k(D)=\max_{x\in F_D}\sum_{i=0}^k\langle g_i,x_i-x\rangle$. The schedule is exactly $\hat\beta_0=\hat\beta_1=1$, $\hat\beta_{i+1}=\hat\beta_i+1/\hat\beta_i$ for $i\ge1$.
--
--   Let $\mu$ be a probability law on an arbitrary measurable sample space $\Xi$. Each feasible section $f(x,\cdot)$ is integrable. Define $\varphi(x)=\int f(x,\xi)\,d\mu(\xi)$ and take expectations over the law $\mu^{\otimes(k+1)}$ of fresh independent samples $\xi_0,\ldots,\xi_k$. The two canonical time-$n$ state maps are a.e. measurable on histories of length $n$ for every $n$. No measurability of the oracle away from the queried history states is assumed.
--
--   Let $x^*\in Q$ minimize $\varphi$ and write $\varphi^*=\varphi(x^*)$. For every $k\ge0$ and every $D\ge d(x^*)$, the normalized gap and each sampled cost are integrable, and
--
--   $$\mathbb E\!\left[\frac{\delta_k(D)}{k+1}\right]\ge\frac1{k+1}\sum_{i=0}^k\mathbb E[f(x_i,\xi_i)]-\varphi^*.$$
--
--   This is the stochastic counterpart of the two pathwise lower bounds.
--
--   Differences from the source:
--   - generalization: the source random cost variables and measurable canonical history states → an arbitrary measurable sample carrier, integrable fixed-input cost sections and a.e.-measurable canonical primal and dual history states; reason: finite-expectation source cost variables are integrable and source measurable states are a.e. measurable under each finite product law; Euclidean sample spaces and completed representatives are included
--   - encoding: functions defined on Q, dual pairings, and SSA paths → ambient extensions used only on Q, continuous-dual evaluation, and canonical finite-history recursion; reason: finite-dimensional duals are continuous; histories compute exactly (6.3), with unit weights and x0 through xk in every average
--   - encoding: maximum over FD for D at least zero → the published real supremum over the same prox level set; reason: the normalized positive strongly convex prox makes FD nonempty compact, so this supremum is attained and finite
--   - encoding: well-defined finite expectations in the stochastic displays → fixed-input cost integrability as a source hypothesis and adaptive integrability as an explicit conclusion; reason: finite real expectations are integrable; making the adaptive conclusion explicit prevents total-integral defaults without imposing an extra oracle condition
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.26, §6, Eq. (6.6)

import Mathlib
import Definitions.Def_NesterovSSAAudit_SSA_randomExecution

set_option autoImplicit false

open Finset MeasureTheory PrimalDualSubgrad.Stoch

namespace NesterovSSAAudit.SSA

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace Ξ]

/-- September 2005 manuscript, p.26, (6.6), with finite expectations asserted. -/
theorem expected_gap_lower_bound
    (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E → Ξ → ℝ) (a : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : RawOracle Q f a L)
    (hsections : ∀ x ∈ Q, Integrable (f x) μ)
    (γ : ℝ) (hγ : 0 < γ) (hrandom : IsRandomExecution μ π γ x0 a)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, population μ f xstar ≤ population μ f x)
    (k : ℕ) (D : ℝ) (hD : d xstar ≤ D) :
    Integrable (fun h : Fin (k + 1) → Ξ =>
      1 / ((k : ℝ) + 1) * pathGap Q d π γ x0 a (padHistory h) k D) (historyLaw μ (k + 1)) ∧
    (∀ i ≤ k, Integrable (fun h : Fin (k + 1) → Ξ =>
      f (pathPoint π γ x0 a (padHistory h) i) (padHistory h i)) (historyLaw μ (k + 1))) ∧
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
        ∫ h : Fin (k + 1) → Ξ, f (pathPoint π γ x0 a (padHistory h) i) (padHistory h i)
          ∂(historyLaw μ (k + 1))
      - population μ f xstar
      ≤ ∫ h : Fin (k + 1) → Ξ,
        1 / ((k : ℝ) + 1) * pathGap Q d π γ x0 a (padHistory h) k D
          ∂(historyLaw μ (k + 1)) := by sorry

end NesterovSSAAudit.SSA
