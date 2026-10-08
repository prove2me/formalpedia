-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_proposition_5
-- name    : HordijkKallenbergLP.Correspondence.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:42.724035+00:00
-- url     : https://prove2.me/theorems/aa6906c3-e557-447b-9605-98a4ad0404cc
-- title:
--   Proposition 5 — recurrent states are exactly E_x
-- statement:
--   Fix positive normalized state weights $\beta$ and any feasible dual solution $(x,y)$. Construct the stationary randomized policy $\pi(x,y)$ by row normalization, and let $P(\pi(x,y))$ be its transition matrix. Then
--
--   $$E_x=\{i:i\text{ is recurrent under }P(\pi(x,y))\}.$$
--
--   This identifies the support of the $x$ flow with the recurrent part of the induced finite Markov chain. Feasibility alone suffices; the dual point need not be optimal or extreme.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 361, Proposition 5

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Model

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), Proposition 5, p. 361.
Formalization Note: the transition matrix uses the normalized policy attached
to the feasible pair, with no extremality or optimality hypothesis. -/
theorem proposition_5 {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1)
    (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ) (hxy : DualFeasible M β x y)
    (π : RandomizedPolicy M)
    (hπ : ∀ i a, π.weight i a = dualPolicyWeight M x y i a) :
    ∀ i, i ∈ Ex M x ↔ IsRecurrent (policyMatrix M π) i := by sorry

end HordijkKallenbergLP.Correspondence
