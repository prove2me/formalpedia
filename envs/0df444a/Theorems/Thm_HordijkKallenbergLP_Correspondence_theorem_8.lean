-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_theorem_8
-- name    : HordijkKallenbergLP.Correspondence.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:33.168234+00:00
-- url     : https://prove2.me/theorems/9a345117-51e1-4637-832a-6a6bb3e3609a
-- title:
--   Theorem 8 — correspondence preserves average optimality
-- statement:
--   Let $\beta_i>0$ with $\sum_i\beta_i=1$ in a finite Markov decision process. There are two directions.
--
--   1. If a stationary randomized policy $\pi^\infty$ is average optimal among all history-dependent randomized policies, then its representative $(x(\pi),y(\pi))$ from equation (6) is an optimal solution of the dual linear program.
--   2. If $(x,y)$ is any optimal dual solution, then its normalized stationary randomized policy $\pi^\infty(x,y)$ exists and is average optimal.
--
--   $$\pi^\infty\text{ average optimal}\Longrightarrow (x(\pi),y(\pi))\text{ dual optimal},\qquad (x,y)\text{ dual optimal}\Longrightarrow\pi^\infty(x,y)\text{ average optimal}.$$
--
--   The theorem relates policy performance to every dual optimum in a multichain model. **Formalization Note** The second direction explicitly constructs a randomized policy with the printed weights; no extreme-point or pure-action hypothesis is imposed.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 360, Theorem 8

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Representative

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), Theorem 8(a) and (b), p. 360.
Formalization Note: part (b) asserts existence of the normalized randomized
policy with the exact printed weights and its average optimality. It ranges over
all dual optima, not only extreme points. -/
theorem theorem_8 {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1) :
    (∀ π : RandomizedPolicy M, HordijkKallenbergLP.SingleLP.IsAvgOptimal M π.toHR →
      DualOptimal M β (representativeX M β π) (representativeY M β π)) ∧
    (∀ x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ, DualOptimal M β x y →
      ∃ π : RandomizedPolicy M,
        (∀ i a, π.weight i a = dualPolicyWeight M x y i a) ∧
        HordijkKallenbergLP.SingleLP.IsAvgOptimal M π.toHR) := by sorry

end HordijkKallenbergLP.Correspondence
