-- Prove2me | Theorems.Thm_N25_canonicalNoncuspPlace25_unit_orders
-- name    : N25.canonicalNoncuspPlace25_unit_orders
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:57.184205+00:00
-- url     : https://prove2.me/theorems/957a9c1f-2cf5-40a4-a09a-cb5d5dd9116e
-- title:
--   The canonical unit functions have order zero at every rational noncusp
-- statement:
--   Let $(x:y:z:w)∈ℙ^3(ℚ)$ be a nonzero rational solution of the canonical quadric and cubic that is not a canonical cusp, and let $P$ be its associated canonical place. For the canonical functions $U$ and $V$, $$\operatorname{ord}_P(U)=0,\qquad \operatorname{ord}_P(V)=0.$$ This places every rational noncusp inside the unit-plane open used for the final arithmetic analysis.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalFunctionCoordinates
import Definitions.Def_N25_CanonicalNoncuspPlace

open N25
open MazurProof.RationalPointsN25CanonicalPoints

theorem N25.canonicalNoncuspPlace25_unit_orders
    (x y z w : ℚ)
    (hnz : NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0)
    (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ IsCanonicalCusp25 x y z w) :
    (canonicalNoncuspPlace25 x y z w hnz hq hc hnc).ord
        canonicalFunctionU25 = 0 ∧
      (canonicalNoncuspPlace25 x y z w hnz hq hc hnc).ord
        canonicalFunctionV25 = 0 := by sorry
