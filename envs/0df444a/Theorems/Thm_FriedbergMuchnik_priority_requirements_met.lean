-- Prove2me | Theorems.Thm_FriedbergMuchnik_priority_requirements_met
-- name    : FriedbergMuchnik.priority_requirements_met
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T20:04:09.289758+00:00
-- url     : https://prove2.me/theorems/d28bf0e5-f55b-44a3-9b8b-c28016a56e23
-- title:
--   The explicit priority construction meets every diagonal requirement
-- statement:
--   Let $A_i=\bigcup_s L_{i,s}$ be the two sets produced by the fixed priority construction. For every side $i\in\{0,1\}$ and every oracle program $c$, there is an input $x\in\mathbb N$ such that
--
--   $$\bigl(x\in A_{1-i}\ \land\ \operatorname{eval}^{\chi_{A_i}}(c,x)\downarrow=0\bigr)\quad\lor\quad\bigl(x\notin A_{1-i}\ \land\ \operatorname{eval}^{\chi_{A_i}}(c,x)\not\downarrow=0\bigr).$$
--
--   Here $\chi_{A_i}$ is the total membership oracle of $A_i$. The notation $\not\downarrow=0$ includes both divergence and convergence to any nonzero natural number. In either alternative, the program fails to compute the characteristic function of $A_{1-i}$ at $x$.
--
--   This is a property of the explicitly defined construction, quantified over all its programs. It assumes neither that a pair of incomparable sets already exists nor that the priority requirements have been satisfied.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51, pp. 53–54, Verification claim and its two permanent-follower outcomes (a) and (b). This statement records the resulting pointwise diagonal witness for FriedbergMuchnik.priorityStage.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem priority_requirements_met (i : Bool) (c : Program) :
    ∃ x : ℕ,
      (x ∈ limitSet (!i) ∧
        0 ∈ oracleEval (Computability.setOracle (limitSet i)) c x) ∨
      (x ∉ limitSet (!i) ∧
        0 ∉ oracleEval (Computability.setOracle (limitSet i)) c x) := by sorry

end FriedbergMuchnik
