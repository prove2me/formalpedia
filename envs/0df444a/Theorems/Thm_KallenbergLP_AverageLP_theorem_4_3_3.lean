-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_3_3
-- name    : KallenbergLP.AverageLP.theorem_4_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:33.281911+00:00
-- url     : https://prove2.me/theorems/1b9cbe66-3b2a-4d16-b3b0-fe01655edc84
-- title:
--   Theorem 4.3.3 — the policy/solution correspondence preserves optimality
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$. The correspondence between the stationary policies and the feasible solutions of the linear program (4.2.11) preserves optimality:
--
--   1. if $\pi^\infty$ is a stationary policy that is average optimal (against all policies), then its representative $(x(\pi),y(\pi))$ of (4.3.2) is an optimal solution of (4.2.11);
--   2. if $(x,y)$ is an optimal solution of (4.2.11), then the weights $\pi_{ia}(x,y)$ of (4.3.1) define a stationary policy, and $\pi^\infty(x,y)$ is average optimal.
--
--   Unlike Theorem 4.2.4, part 2 needs no extreme-point assumption, but it produces a randomized policy in general.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 112, Theorem 4.3.3

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.3.3.** The correspondence between the stationary policies and the feasible solutions
of the linear program (4.2.11) preserves the optimality property, i.e.
1. if `π^∞` is a stationary average optimal policy, then `(x(π), y(π))` is an optimal solution of
   (4.2.11);
2. if `(x, y)` is an optimal solution of (4.2.11), then the stationary policy `π^∞(x, y)` is an
   average optimal policy.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 112, Theorem 4.3.3.

**Formalization Note.** In part 2 the conclusion also records that the weights (4.3.1) form a
stationary policy, and then that every stationary policy with these weights is average optimal. -/
theorem theorem_4_3_3 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1) :
    (∀ π : StatPolicy M, IsAvgOptimal M π.toHR → IsDualOptimal M β (xRep M β π, yRep M β π)) ∧
    ∀ z : (Pair M → ℝ) × (Pair M → ℝ), IsDualOptimal M β z →
      (∃ π : StatPolicy M, π.weight = dualPolicyWeight M z.1 z.2) ∧
      ∀ π : StatPolicy M, π.weight = dualPolicyWeight M z.1 z.2 → IsAvgOptimal M π.toHR := by sorry

end KallenbergLP.AverageLP
