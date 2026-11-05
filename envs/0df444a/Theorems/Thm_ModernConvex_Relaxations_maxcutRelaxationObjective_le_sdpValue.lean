-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_maxcutRelaxationObjective_le_sdpValue
-- name    : ModernConvex.Relaxations.maxcutRelaxationObjective_le_sdpValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:28.14675+00:00
-- url     : https://prove2.me/theorems/4c290670-9fc6-44c1-a934-d6d70e05eadd
-- title:
--   Every feasible point bounds the MAXCUT SDP value from below
-- statement:
--   Let $a$ be a real matrix and let $S$ be the optimal value of the Max-Cut semidefinite relaxation $\max\{\tfrac14\sum_{i,j}a_{ij}(1-X_{ij}) : X\succeq 0,\ X_{ii}=1\}$, in the sense of being the least upper bound of the objective over the feasible set. Then every feasible $X$ satisfies $\tfrac14\sum_{i,j}a_{ij}(1-X_{ij})\le S$.
--
--   Immediate from the definition of a least upper bound; recorded because it is the lower half of the two-sided squeeze that turns a numerical certificate into a bound.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; primal half of the SDP squeeze.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **Primal bound.** Every feasible `X` gives a lower bound on the optimal SDP value. -/
theorem maxcutRelaxationObjective_le_sdpValue {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsUnitDiagPSD X) {S : ℝ}
    (hS : IsMaxcutSDPValue a S) : maxcutRelaxationObjective a X ≤ S := by sorry

end ModernConvex.Relaxations
