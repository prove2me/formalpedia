-- Prove2me | Theorems.Thm_FriedbergMuchnik_stage_membership_computable
-- name    : FriedbergMuchnik.stage_membership_computable
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T20:04:05.257493+00:00
-- url     : https://prove2.me/theorems/502b32d4-b5c0-4056-8dd3-94dad511a019
-- title:
--   Computability of membership in the explicit priority stages
-- statement:
--   For the fixed finite-stage construction in the imported definition bundle, let $L_{i,s}$ be the list of numbers enumerated on side $i\in\{0,1\}$ by stage $s\in\mathbb N$. The relation
--
--   $$\{(s,i,n):n\in L_{i,s}\}$$
--
--   is computable, uniformly in the stage, side, and natural-number input. All stages, including stage zero, are included.
--
--   The lists are produced by the specified least-requirement priority step and bounded oracle interpreter. This theorem supplies the effectiveness assertion needed to show their unions are c.e.; it makes no assumption that the construction's stages are computable.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51, pp. 52–53, Construction and the assertion that the finite-stage sequence is recursive. This is the stage-membership consequence for the explicit syntax, bounded simulation, and list representation in FriedbergMuchnik.priorityStage.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem stage_membership_computable :
    ComputablePred (fun p : ℕ × (Bool × ℕ) => p.2.2 ∈ stageList p.2.1 p.1) := by sorry

end FriedbergMuchnik
