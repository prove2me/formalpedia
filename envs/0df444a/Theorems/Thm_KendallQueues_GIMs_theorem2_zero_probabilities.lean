-- Prove2me | Theorems.Thm_KendallQueues_GIMs_theorem2_zero_probabilities
-- name    : KendallQueues.GIMs.theorem2_zero_probabilities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:07.376136+00:00
-- url     : https://prove2.me/theorems/76c53020-af25-4f54-b000-2ae4b678718e
-- title:
--   Theorem II, p. 349 — the equilibrium probabilities that Q and w are zero
-- statement:
--   Consider GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$, exponential service of mean $b>0$, transition matrix $P$ of (8)–(14), and $\rho=b/(sa)<1$. Let $\lambda$ be a root of $F(\lambda)=\lambda$ in $0<\lambda<1$, and let $\mu_0,\dots,\mu_{s-2}$ be such that the trial vector $x=[\mu_0,\dots,\mu_{s-2},1,\lambda,\lambda^2,\dots]$ satisfies $x_j=\sum_\alpha x_\alpha p_{\alpha j}$ for $1\le j\le s-1$. Write $\sum\mu=\mu_0+\dots+\mu_{s-2}$ ($0$ when $s=1$).
--
--   Then the limiting distribution $\pi$ of the chain ($p^n_{ij}\to\pi_j$, $\sum_j\pi_j=1$) exists, and in this statistical equilibrium the probability that the queue size $Q=\max(i-s,0)$ is zero is
--   $$\alpha=\frac{\sum\mu+1+\lambda}{\sum\mu+1/(1-\lambda)},$$
--   and the probability that the waiting time $w$ is zero is
--   $$\beta=\frac{\sum\mu+1}{\sum\mu+1/(1-\lambda)}.$$
--
--   **Formalization Note** $\Pr(Q=0)=\sum_{i\le s}\pi_i$ (`queueLaw s π 0`) and $\Pr(w=0)=\Pr(w\le0)$ is the Erlang-mixture distribution function at $0$ (`waitCDF s b π 0`). The $\mu$'s are characterized by the invariance equations, as on the page; they are not defined from $\pi$.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 349, Theorem II, eqs. (18)–(20)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- Theorem II, p. 349: with `λ` the root of `F(λ) = λ` in `(0, 1)` and `μ_0, …, μ_{s-2}` the
`μ`-terms determined by the invariance equations for `1 ≤ j ≤ s - 1`, in equilibrium
`P(Q = 0) = α = (∑μ + 1 + λ)/(∑μ + 1/(1-λ))` and `P(w = 0) = β = (∑μ + 1)/(∑μ + 1/(1-λ))`. -/
theorem theorem2_zero_probabilities (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (hρ : rho s a b < 1)
    (P : TransitionMatrix) (hP : P.p = gimsMatrix s A b)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hF : F s A b lam = lam)
    (μ : Fin (s - 1) → ℝ)
    (hμ : ∀ j : ℕ, 1 ≤ j → j ≤ s - 1 →
      HasSum (fun α => trialVector s μ lam α * P.p α j) (trialVector s μ lam j)) :
    ∃ π : ℕ → ℝ, HasSum π 1 ∧
      (∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (π j))) ∧
      queueLaw s π 0 = ((∑ k, μ k) + 1 + lam) / ((∑ k, μ k) + 1 / (1 - lam)) ∧
      waitCDF s b π 0 = ((∑ k, μ k) + 1) / ((∑ k, μ k) + 1 / (1 - lam)) := by sorry

end KendallQueues.GIMs
