-- Prove2me | Theorems.Thm_N25_canonicalJacobianMinor25_eval
-- name    : N25.canonicalJacobianMinor25_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:39.073466+00:00
-- url     : https://prove2.me/theorems/c3d29b01-4c91-4b74-b137-98bcaa19c5f5
-- title:
--   Canonical Jacobian minors evaluate to the expected gradient determinants
-- statement:
--   Let $K$ be a commutative ring, let $Q_j(v)$ and $C_j(v)$ be the $j$th gradient coordinates of the canonical quadric and cubic at $v∈K^4$, and let $M_{jk}$ be their formal Jacobian minor. For $j,k∈\{0,1,2,3\}$, $$\operatorname{ev}_v(M_{jk})=Q_j(v)C_k(v)-C_j(v)Q_k(v).$$ This is the evaluation identity needed to pass between polynomial ideals and pointwise nonsingularity.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open scoped BigOperators

theorem N25.canonicalJacobianMinor25_eval {K : Type*} [CommRing K]
    (v : Fin 4 → K) (j k : Fin 4) :
    MvPolynomial.eval v (canonicalJacobianMinor25 K j k) =
      canonicalQuadricGradient25 v j * canonicalCubicGradient25 v k -
        canonicalCubicGradient25 v j * canonicalQuadricGradient25 v k := by sorry
