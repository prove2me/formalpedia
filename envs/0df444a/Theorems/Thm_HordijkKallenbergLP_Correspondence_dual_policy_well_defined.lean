-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_dual_policy_well_defined
-- name    : HordijkKallenbergLP.Correspondence.dual_policy_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:36.238122+00:00
-- url     : https://prove2.me/theorems/67be23e9-1edc-4c5c-9306-5821c23a0139
-- title:
--   §3.2 — normalization of a feasible dual solution
-- statement:
--   Let $\beta_i>0$ with $\sum_i\beta_i=1$, and let $(x,y)$ satisfy the dual constraints (3)–(5). For every state $j$,
--
--   $$\sum_{a\in A(j)}x_{ja}+\sum_{a\in A(j)}y_{ja}\ge\beta_j>0.$$
--
--   Consequently the normalized rule $\pi_{ja}(x,y)$, using $x$ when its row sum is positive and $y$ otherwise, is a stationary randomized policy supported on available actions. This supplies the denominator and policy facts used in both parts of Theorem 8. **Formalization Note** The Lean inequality states the comparison with $\beta_j$; strict positivity follows from the separately stated assumption $\beta_j>0$.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, §3.2, proof of Theorem 7

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Model

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), §3.2, proof of Theorem 7, p. 357:
equations (4) and (5) make the normalization of §3.3 a policy.
Formalization Note: the existence clause certifies both cases of the printed
definition, including the positive y-denominator outside E_x. -/
theorem dual_policy_well_defined {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1)
    (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ) (hxy : DualFeasible M β x y) :
    (∀ i, β i ≤ stateMass M x i + stateMass M y i) ∧
    ∃ π : RandomizedPolicy M, ∀ i a, π.weight i a = dualPolicyWeight M x y i a := by sorry

end HordijkKallenbergLP.Correspondence
