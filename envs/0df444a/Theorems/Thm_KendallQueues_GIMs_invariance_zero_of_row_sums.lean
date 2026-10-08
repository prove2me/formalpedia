-- Prove2me | Theorems.Thm_KendallQueues_GIMs_invariance_zero_of_row_sums
-- name    : KendallQueues.GIMs.invariance_zero_of_row_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:35.37287+00:00
-- url     : https://prove2.me/theorems/b0bd7e4e-ab92-4ecb-95ff-51923e3a1fbc
-- title:
--   §7, p. 349 — the invariance condition at state 0 follows from the row sums
-- statement:
--   Let $P=[p_{ij}]$, $i,j\ge0$, be a stochastic matrix (nonnegative entries, every row summing to one), and let $x=(x_0,x_1,\dots)$ be a real vector with $\sum_\alpha|x_\alpha|<\infty$ that satisfies the invariance conditions
--   $$x_j=\sum_{\alpha=0}^{\infty}x_\alpha p_{\alpha j}\qquad(j=1,2,3,\dots).$$
--   Then it also satisfies the last one,
--   $$x_0=\sum_{\alpha=0}^{\infty}x_\alpha p_{\alpha 0}.$$
--
--   In the paper this closes the construction of the invariant vector of the GI/M/s chain: once the equations for $j\ge1$ hold, the one for $j=0$ comes from the row sums.
--
--   **Formalization Note** The statement is the general fact the page invokes, for any `TransitionMatrix`, rather than its GI/M/s instance. Absolute summability of $x$ is the paper's standing requirement on the trial vector ("absolutely convergent series", p. 348). Each invariance equation is stated with `HasSum`.
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

/-- §7, p. 349: for a stochastic matrix (row sums equal to one), an absolutely summable vector
satisfying every invariance equation except the one for state `0` satisfies that one too. -/
theorem invariance_zero_of_row_sums (P : TransitionMatrix) (x : ℕ → ℝ)
    (habs : Summable (fun i => |x i|))
    (heq : ∀ j, j ≠ 0 → HasSum (fun α => x α * P.p α j) (x j)) :
    HasSum (fun α => x α * P.p α 0) (x 0) := by sorry

end KendallQueues.GIMs
