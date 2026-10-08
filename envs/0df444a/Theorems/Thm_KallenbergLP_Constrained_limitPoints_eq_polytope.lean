-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_limitPoints_eq_polytope
-- name    : KallenbergLP.Constrained.limitPoints_eq_polytope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:45.674981+00:00
-- url     : https://prove2.me/theorems/fc4b412a-6137-4a94-b1ae-18995093220d
-- title:
--   Theorem 4.7.2 — L = X: the limit points of the expected state-action frequencies form the LP polytope
-- statement:
--   Let $\beta$ be an initial distribution ($\beta_j\ge0$, $\sum_j\beta_j=1$; zeros allowed) for a finite Markov decision model with stochastic transitions $p_{iaj}$. Let $L$ be the set of all limit points of the expected state-action frequencies
--
--   $$x^T_{ja}(R)=\frac1T\sum_{t=1}^T\sum_i\beta_i\,\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i)$$
--
--   over all policies $R$ (history-dependent and randomized), and let $X$ be the set of vectors $x$ for which some $y$ satisfies
--
--   $$\sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia}=0,\qquad\sum_a x_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})y_{ia}=\beta_j\quad(j\in E),\qquad x_{ia},y_{ia}\ge0.$$
--
--   Then
--
--   $$L=X.$$
--
--   This characterizes the achievable long-run state-action frequencies of a multichain Markov decision problem as a polytope described by finitely many linear constraints, which is what makes constrained average-reward problems solvable by a single linear program.
--
--   **Formalization Note** $L$ ranges over all history-dependent randomized policies; restricting to stationary policies would give $L(S)$, which differs from $X$ in general (Example 4.7.1 of the book).
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 138, Theorem 4.7.2

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.2, p. 138: `L = X`. The set of all limit points of the expected
state-action frequencies, over all (history-dependent, randomized) policies, equals the polytope
`X` of (4.7.8). -/
theorem limitPoints_eq_polytope {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) :
    Lset M β (fun _ => True) = polytopeX M β := by sorry

end KallenbergLP.Constrained
