-- Prove2me | Theorems.Thm_NesterovSSAAudit_SSA_pathwise_gap_bound
-- name    : NesterovSSAAudit.SSA.pathwise_gap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:49.076023+00:00
-- url     : https://prove2.me/theorems/5455fd85-9d9b-42b0-95c9-df0309159b8e
-- title:
--   §6, Eq. (6.5) — uniform pathwise SSA gap bound
-- statement:
--   Let $E$ be a finite-dimensional real normed space with continuous dual $E^*$, and $Q\subseteq E$ nonempty closed and convex. Let $d$ be continuous on $Q$, strongly convex with parameter $\sigma>0$, and normalized at its minimizing prox-center $x_0$ by $d(x_0)=0$. Let $\pi_\beta(s)$ be the exact minimizer of $-\langle s,x\rangle+\beta d(x)$ on $Q$ for $\beta>0$. Let $\Xi$ be a sample carrier, $f:E\times\Xi\to\mathbb R$ the cost, $a:E\times\Xi\to E^*$ the oracle and $L\ge0$ their bound, satisfying the pointwise convexity, relative-subgradient and dual-norm-bound assumptions, and let $\gamma>0$. Starting with $s_0=0$ and the prox-center $x_0$, compute $g_i=a(x_i,\xi_i)$, $s_{i+1}=s_i+g_i$ and $x_{i+1}=\pi_{\gamma\hat\beta_{i+1}}(-s_{i+1})$. Write $\bar x_k=(k+1)^{-1}\sum_{i=0}^k x_i$, $F_D=\{x\in Q:d(x)\le D\}$, and $\delta_k(D)=\max_{x\in F_D}\sum_{i=0}^k\langle g_i,x_i-x\rangle$. The schedule is exactly $\hat\beta_0=\hat\beta_1=1$, $\hat\beta_{i+1}=\hat\beta_i+1/\hat\beta_i$ for $i\ge1$.
--
--   For every observation path, every $k\ge0$ and every $D\ge0$,
--
--   $$\frac{\delta_k(D)}{k+1}\le\frac{\hat\beta_{k+1}}{k+1}\left(\gamma D+\frac{L^2}{2\sigma\gamma}\right).$$
--
--   This is the uniform pathwise accuracy certificate used by the stochastic expected-error theorem.
--
--   Differences from the source:
--   - generalization: sample paths of a solvable stochastic probability model with finite fixed-input expectations → every path in an arbitrary sample carrier, without probability data, section integrability or population solvability; reason: the displayed claims are pointwise; every source run is one such path
--   - encoding: functions defined on Q, dual pairings, and SSA paths → ambient extensions used only on Q, continuous-dual evaluation, and canonical finite-history recursion; reason: finite-dimensional duals are continuous; histories compute exactly (6.3), with unit weights and x0 through xk in every average
--   - encoding: maximum over FD for D at least zero → the published real supremum over the same prox level set; reason: the normalized positive strongly convex prox makes FD nonempty compact, so this supremum is attained and finite
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.26, §6, Eq. (6.5)

import Mathlib
import Definitions.Def_NesterovSSAAudit_SSA_historyStates

set_option autoImplicit false

open Finset MeasureTheory PrimalDualSubgrad.Stoch

namespace NesterovSSAAudit.SSA

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- September 2005 manuscript, p.26, (6.5), for every path, without probability data. -/
theorem pathwise_gap_bound
    (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (f : E → Ξ → ℝ) (a : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : RawOracle Q f a L)
    (γ : ℝ) (hγ : 0 < γ) (ω : ℕ → Ξ) (k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    1 / ((k : ℝ) + 1) * pathGap Q d π γ x0 a ω k D
      ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * D + L ^ 2 / (2 * σ * γ)) := by sorry

end NesterovSSAAudit.SSA
