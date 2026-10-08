-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_6
-- name    : HordijkKallenbergLP.SingleLP.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:56:38.560979+00:00
-- url     : https://prove2.me/theorems/bee177bd-0552-4638-a586-378edc2bf943
-- title:
--   Theorem 6 — φ is the smallest function admitting u with (φ, u) superharmonic
-- statement:
--   Let $\varphi_i=\sup_R\varphi_i(R)$ be the optimal average reward. Then $\varphi$ is the componentwise smallest function for which there exists a function $u$ such that $(\varphi,u)$ is superharmonic:
--
--   1. there is $u:E\to\mathbb R$ with $(\varphi,u)$ superharmonic, and
--   2. whenever $(\tilde\varphi,\tilde u)$ is superharmonic,
--   $$\varphi_i\le\tilde\varphi_i\qquad\text{for every }i\in E .$$
--
--   This characterization motivates the primal linear program of §3.2, whose optimal solutions have first component $\varphi$.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, Theorem 6

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 6.** `φ` is the (componentwise) smallest function for which there exists a function
`u` such that `(φ, u)` is superharmonic. Here `φ_i = sup_R φ_i(R)` is the optimal average reward.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, Theorem 6.

**Formalization Note.** Both halves are stated: some `u` makes `(φ, u)` superharmonic, and
`φ ≤ φ̃` componentwise for every superharmonic `(φ̃, ũ)`. -/
theorem theorem_6 (M : StationaryMDP S A) [Nonempty S] :
    (∃ u : S → ℝ, Superharmonic M (optGainInf M) u) ∧
      ∀ φ' u' : S → ℝ, Superharmonic M φ' u' → ∀ i, optGainInf M i ≤ φ' i := by sorry

end HordijkKallenbergLP.SingleLP
