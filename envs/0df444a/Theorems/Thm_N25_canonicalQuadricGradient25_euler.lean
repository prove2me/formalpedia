-- Prove2me | Theorems.Thm_N25_canonicalQuadricGradient25_euler
-- name    : N25.canonicalQuadricGradient25_euler
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:27.019375+00:00
-- url     : https://prove2.me/theorems/b415028b-bdce-41f7-8016-f5e480dfbb52
-- title:
--   Euler’s identity holds for the canonical quadric
-- statement:
--   Let $K$ be a commutative ring, let $Q$ be the homogeneous canonical quadric, and let $Q_j(v)$ denote its gradient coordinates at $v∈K^4$. Then $$\sum_{j=0}^{3}v_jQ_j(v)=2Q(v_0,v_1,v_2,v_3).$$ This homogeneous Euler identity relates the defining equation to its Jacobian row.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open scoped BigOperators

theorem N25.canonicalQuadricGradient25_euler {K : Type*} [CommRing K] (v : Fin 4 → K) :
    ∑ j : Fin 4, v j * canonicalQuadricGradient25 v j =
      2 * canonicalQuadric (v 0) (v 1) (v 2) (v 3) := by sorry
