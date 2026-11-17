-- Prove2me | Theorems.Thm_N25_canonicalQuadricGradient25_eval
-- name    : N25.canonicalQuadricGradient25_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:35.823314+00:00
-- url     : https://prove2.me/theorems/039b49c2-a19e-47b0-bc2c-f07da313ce00
-- title:
--   The explicit quadric gradient equals formal differentiation
-- statement:
--   Let $K$ be a commutative ring, let $Q∈K[X_0,X_1,X_2,X_3]$ be the canonical quadric, let $v=(v_0,v_1,v_2,v_3)∈K^4$, and let $j∈\{0,1,2,3\}$. If $Q_j(v)$ denotes the explicitly defined $j$th gradient coordinate, then $$\operatorname{ev}_v(∂_jQ)=Q_j(v).$$ This identifies the computational gradient with the multivariable-polynomial derivative used in the Jacobian criterion.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open scoped BigOperators

theorem N25.canonicalQuadricGradient25_eval {K : Type*} [CommRing K]
    (v : Fin 4 → K) (j : Fin 4) :
    MvPolynomial.eval v
      (MvPolynomial.pderiv j (canonicalQuadric
        (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3))) =
      canonicalQuadricGradient25 v j := by sorry
