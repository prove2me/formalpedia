-- Prove2me | Theorems.Thm_NesterovSSAAudit_SSA_pathwise_gap_lower_bound
-- name    : NesterovSSAAudit.SSA.pathwise_gap_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:43:32.077294+00:00
-- url     : https://prove2.me/theorems/70aa0341-753d-42da-8b4d-3e5b2491fdad
-- title:
--   §6, display after (6.5) — both gap lower bounds
-- statement:
--   Let $E$ be a finite-dimensional real normed space with continuous dual $E^*$, and $Q\subseteq E$ nonempty closed and convex. Let $d$ be continuous on $Q$, strongly convex with parameter $\sigma>0$, and normalized at its minimizing prox-center $x_0$ by $d(x_0)=0$. Let $\pi_\beta(s)$ be the exact minimizer of $-\langle s,x\rangle+\beta d(x)$ on $Q$ for $\beta>0$. Let $\Xi$ be a sample carrier, $f:E\times\Xi\to\mathbb R$ the cost, $a:E\times\Xi\to E^*$ the oracle and $L\ge0$ their bound, satisfying the pointwise convexity, relative-subgradient and dual-norm-bound assumptions, and let $\gamma>0$. Starting with $s_0=0$ and the prox-center $x_0$, compute $g_i=a(x_i,\xi_i)$, $s_{i+1}=s_i+g_i$ and $x_{i+1}=\pi_{\gamma\hat\beta_{i+1}}(-s_{i+1})$. Write $\bar x_k=(k+1)^{-1}\sum_{i=0}^k x_i$, $F_D=\{x\in Q:d(x)\le D\}$, and $\delta_k(D)=\max_{x\in F_D}\sum_{i=0}^k\langle g_i,x_i-x\rangle$. The schedule is exactly $\hat\beta_0=\hat\beta_1=1$, $\hat\beta_{i+1}=\hat\beta_i+1/\hat\beta_i$ for $i\ge1$.
--
--   For every feasible comparator $x^*\in Q$, every $D\ge d(x^*)$, every path and every $k\ge0$,
--
--   $$\frac{\delta_k(D)}{k+1}\ge\frac1{k+1}\sum_{i=0}^k\langle a(x_i,\xi_i),x_i-x^*\rangle\ge\frac1{k+1}\sum_{i=0}^k[f(x_i,\xi_i)-f(x^*,\xi_i)].$$
--
--   Both inequalities are retained. The comparator need not be a population minimizer. This links the certificate to sampled objective differences.
--
--   Differences from the source:
--   - generalization: sample paths of a solvable stochastic probability model with finite fixed-input expectations → every path in an arbitrary sample carrier, without probability data, section integrability or population solvability; reason: the displayed claims are pointwise; every source run is one such path
--   - generalization: the optimizer xstar in the display after (6.5) → every feasible comparator xstar; reason: both inequalities use only membership of xstar in FD and the relative subgradient inequality
--   - encoding: functions defined on Q, dual pairings, and SSA paths → ambient extensions used only on Q, continuous-dual evaluation, and canonical finite-history recursion; reason: finite-dimensional duals are continuous; histories compute exactly (6.3), with unit weights and x0 through xk in every average
--   - encoding: maximum over FD for D at least zero → the published real supremum over the same prox level set; reason: the normalized positive strongly convex prox makes FD nonempty compact, so this supremum is attained and finite
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.26, §6, display after (6.5)

import Mathlib
import Definitions.Def_NesterovSSAAudit_SSA_historyStates

set_option autoImplicit false

open Finset MeasureTheory PrimalDualSubgrad.Stoch

namespace NesterovSSAAudit.SSA

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- September 2005 manuscript, p.26, display after (6.5): both inequalities.
Every feasible comparator works, with no population-optimality assumption. -/
theorem pathwise_gap_lower_bound
    (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (f : E → Ξ → ℝ) (a : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : RawOracle Q f a L)
    (γ : ℝ) (hγ : 0 < γ) (ω : ℕ → Ξ) (k : ℕ)
    (xstar : E) (hxstar : xstar ∈ Q) (D : ℝ) (hD : d xstar ≤ D) :
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
        pathAnswer π γ x0 a ω i (pathPoint π γ x0 a ω i - xstar)
      ≤ 1 / ((k : ℝ) + 1) * pathGap Q d π γ x0 a ω k D ∧
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
        (f (pathPoint π γ x0 a ω i) (ω i) - f xstar (ω i))
      ≤ 1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
        pathAnswer π γ x0 a ω i (pathPoint π γ x0 a ω i - xstar) := by sorry

end NesterovSSAAudit.SSA
