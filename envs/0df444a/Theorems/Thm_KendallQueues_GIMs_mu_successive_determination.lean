-- Prove2me | Theorems.Thm_KendallQueues_GIMs_mu_successive_determination
-- name    : KendallQueues.GIMs.mu_successive_determination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:19.209536+00:00
-- url     : https://prove2.me/theorems/5b250812-d510-45f8-a430-2f0466b2b241
-- title:
--   §7, p. 349 — the equations for 1 ≤ j ≤ s − 1 determine the μ's of the trial vector
-- statement:
--   Consider GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$ and exponential service of mean $b>0$, with transition matrix $P=[p_{ij}]$ of (8)–(14), and let $0<\lambda<1$. Then there is exactly one choice of real numbers $\mu_0,\dots,\mu_{s-2}$ such that the trial vector
--   $$x=[\mu_0,\dots,\mu_{s-2},1,\lambda,\lambda^2,\dots]$$
--   of (15) satisfies the invariance equations
--   $$x_j=\sum_{\alpha=0}^{\infty}x_\alpha p_{\alpha j}\qquad(1\le j\le s-1),$$
--   each series converging to $x_j$.
--
--   This is the "successive determination of the $\mu$'s"; together with the reduction of the equations for $j\ge s$ to $F(\lambda)=\lambda$ and the equation for $j=0$ it produces an invariant vector.
--
--   **Formalization Note** "Successive determination" is read as existence and uniqueness of the $\mu$'s (`∃!`). For $s=1$ there are no $\mu$'s and no equations, and the statement holds trivially, as on the page; the hypothesis $1\le s$ is kept.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 349

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- §7, p. 349: for `0 < x < 1` the invariance equations `x_j = ∑_α x_α p_{αj}`,
`1 ≤ j ≤ s - 1`, determine the `μ`-terms of the trial vector (15) uniquely. -/
theorem mu_successive_determination (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ∃! μ : Fin (s - 1) → ℝ, ∀ j : ℕ, 1 ≤ j → j ≤ s - 1 →
      HasSum (fun α => trialVector s μ x α * gimsMatrix s A b α j) (trialVector s μ x j) := by sorry

end KendallQueues.GIMs
