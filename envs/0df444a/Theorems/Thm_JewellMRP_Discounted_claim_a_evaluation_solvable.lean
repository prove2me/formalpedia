-- Prove2me | Theorems.Thm_JewellMRP_Discounted_claim_a_evaluation_solvable
-- name    : JewellMRP.Discounted.claim_a_evaluation_solvable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:59:47.330071+00:00
-- url     : https://prove2.me/theorems/81338726-d8dc-4147-8799-cedb9f323b28
-- title:
--   Claim (a), p. 946 — the value-determination equations (15) are uniquely solvable
-- statement:
--   Let a Markov-renewal program be given and let $\alpha > 0$. For every stationary policy $d$ there is exactly one vector $v = (v_i)_{i \in S}$ with
--   $$
--   v_i = \rho^{d(i)}_i(\alpha) + \sum_{j} p^{d(i)}_{ij}\,\tilde f^{d(i)}_{ij}(\alpha)\, v_j \qquad \text{for all } i \in S .
--   $$
--
--   The paper writes "(a) It is always possible to solve the set of simultaneous equations"; the argument it refers to (Howard's value-determination step) establishes existence and uniqueness of the solution, which is what the policy-iteration algorithm of Fig. 1 needs to have a well-defined "present expected return" in each cycle.
--
--   **Formalization Note** The solution is stated as a unique existence, not through a matrix inverse (which is $0$ for a singular matrix in Mathlib). The equations are those of (15) for the policy $d$.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 946, Claim (a) (equations (15), p. 945)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (a), p. 946: for every `α > 0` and every stationary policy `d`, the
value-determination equations (15) have exactly one solution. -/
theorem claim_a_evaluation_solvable {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) : ∃! v : S → ℝ, SolvesEval M α d v := by sorry

end JewellMRP.Discounted
