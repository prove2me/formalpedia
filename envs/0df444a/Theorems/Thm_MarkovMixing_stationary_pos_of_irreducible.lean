-- Prove2me | Theorems.Thm_MarkovMixing_stationary_pos_of_irreducible
-- name    : MarkovMixing.stationary_pos_of_irreducible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:03.018411+00:00
-- url     : https://prove2.me/theorems/e38e3e44-0c3d-4a63-b1d4-27ac712c85df
-- title:
--   The stationary distribution of an irreducible chain is strictly positive
-- statement:
--   Let $P$ be a stochastic matrix on a finite state space $V$ which is irreducible, so that
--   for every pair of states $x, y$ some power satisfies $(P^{t})(x,y) > 0$. Let $\pi$ be a
--   stationary distribution for $P$. Then $\pi$ charges every state:
--
--   $$
--   \pi(x) \;>\; 0 \qquad \text{for every } x \in V .
--   $$
--
--   Irreducibility rules out the degenerate case of a stationary distribution supported on a proper
--   subset of the state space. The consequence is used constantly and rarely stated: it is what makes
--   $\langle f, g\rangle_\pi = \sum_x \pi(x) f(x) g(x)$ an inner product rather than a degenerate
--   form, and what allows division by $\pi(x)$ in Dirichlet-form and spectral computations.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Proposition 1.14 and §1.5; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MarkovMixing.stationary_pos_of_irreducible {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by sorry
