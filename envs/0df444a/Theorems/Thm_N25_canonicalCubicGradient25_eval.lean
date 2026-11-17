-- Prove2me | Theorems.Thm_N25_canonicalCubicGradient25_eval
-- name    : N25.canonicalCubicGradient25_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:44.770892+00:00
-- url     : https://prove2.me/theorems/720ffd49-6992-41ac-b4ee-2effbacc05c5
-- title:
--   The explicit cubic gradient equals formal differentiation
-- statement:
--   Let $K$ be a commutative ring, let $C∈K[X_0,X_1,X_2,X_3]$ be the canonical cubic, let $v∈K^4$, and let $j∈\{0,1,2,3\}$. If $C_j(v)$ is the explicitly defined $j$th gradient coordinate, then $$\operatorname{ev}_v(∂_jC)=C_j(v).$$ This connects the concrete formulas used in finite computations with the formal Jacobian matrix.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open scoped BigOperators

theorem N25.canonicalCubicGradient25_eval {K : Type*} [CommRing K]
    (v : Fin 4 → K) (j : Fin 4) :
    MvPolynomial.eval v
      (MvPolynomial.pderiv j (canonicalCubic
        (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3))) =
      canonicalCubicGradient25 v j := by sorry
