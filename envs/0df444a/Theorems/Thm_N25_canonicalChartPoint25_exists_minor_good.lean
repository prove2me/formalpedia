-- Prove2me | Theorems.Thm_N25_canonicalChartPoint25_exists_minor_good
-- name    : N25.canonicalChartPoint25_exists_minor_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:24.967973+00:00
-- url     : https://prove2.me/theorems/4ec1d4cd-d258-4f7a-9be7-ab812f0c5133
-- title:
--   A nonpivot Jacobian minor is nonzero in characteristics $2$ and $3$
-- statement:
--   Let $p$ be a prime with $p=2$ or $p=3$, let $K$ be a field of characteristic $p$, fix a chart pivot $i∈\{0,1,2,3\}$, and let $P$ be a $K$-valued point of the corresponding canonical affine chart. Let $M_{jk}$ denote the $2×2$ minor formed from columns $j$ and $k$ of the Jacobian matrix of the canonical quadric and cubic, and put $I_i=\{0,1,2,3\}\setminus\{i\}$. Then $$∃j,k∈I_i,\ j<k ∧ M_{jk}(P)≠0.$$ This supplies the pointwise Jacobian certificate for smoothness at both good primes. Formalization note: primality of $p$ is carried by a typeclass witness.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open scoped BigOperators
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientKummerThreeProjective

theorem N25.canonicalChartPoint25_exists_minor_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (i : Fin 4)
    (P : CanonicalChartPoint25 K i) :
    ∃ j k : Fin 4, j ≠ i ∧ k ≠ i ∧ j < k ∧
      MvPolynomial.eval P.coordinates (canonicalJacobianMinor25 K j k) ≠ 0 := by sorry
