-- Prove2me | Theorems.Thm_KendallQueues_GIMs_normalized_limit
-- name    : KendallQueues.GIMs.normalized_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:51.274987+00:00
-- url     : https://prove2.me/theorems/cde5192a-5ac4-4bff-975d-f6cc28f99001
-- title:
--   §7, p. 348 — a nonnull summable invariant vector, normalized, is the limiting distribution
-- statement:
--   Let $P=[p_{ij}]$, $i,j\ge0$, be the transition matrix of an irreducible, aperiodic Markov chain, with $n$-step transition probabilities $p^n_{ij}$. Suppose that $x=(x_0,x_1,\dots)$ is a real vector, not identically zero, with $\sum_\alpha|x_\alpha|<\infty$, which is invariant:
--   $$x_j=\sum_{\alpha=0}^{\infty}x_\alpha p_{\alpha j}\qquad(j=0,1,2,\dots).$$
--   Then $\sum_\alpha x_\alpha\neq0$, and for all states $i,j$
--   $$p^n_{ij}\to\pi_j=\frac{x_j}{\sum_\alpha x_\alpha}\qquad(n\to\infty),$$
--   where every $\pi_j$ is positive.
--
--   The signs of the components of $x$ do not matter. This is how the paper turns the invariant trial vector of GI/M/s into the limiting distribution of the chain.
--
--   **Formalization Note** Irreducibility and aperiodicity are the published predicates. The page derives the statement from Feller's dichotomy (every state transient or null, with $p^n_{ij}\to0$; or every state ergodic, with $p^n_{ij}\to\pi_j>0$, $\sum\pi_j=1$); that ergodicity follows is the referenced Foster sufficiency theorem and is not repeated here. The invariance equations are stated with `HasSum`.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 348

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- §7, p. 348: for an irreducible aperiodic chain with a nonnull, absolutely summable invariant
vector `x`, `∑ x_α ≠ 0` and `p^n_{ij} → x_j / ∑ x_α` for all `i, j`, the limits being positive. -/
theorem normalized_limit (P : TransitionMatrix) (hirr : P.Irreducible) (hap : P.Aperiodic)
    (x : ℕ → ℝ) (hnonnull : ∃ i, x i ≠ 0) (habs : Summable (fun i => |x i|))
    (heq : ∀ j, HasSum (fun α => x α * P.p α j) (x j)) :
    (∑' α, x α) ≠ 0 ∧
      (∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (x j / ∑' α, x α))) ∧
      ∀ j, 0 < x j / ∑' α, x α := by sorry

end KendallQueues.GIMs
