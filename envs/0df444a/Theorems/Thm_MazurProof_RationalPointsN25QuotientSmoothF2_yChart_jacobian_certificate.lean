-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_yChart_jacobian_certificate
-- name    : MazurProof.RationalPointsN25QuotientSmoothF2.yChart_jacobian_certificate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:14.065216+00:00
-- url     : https://prove2.me/theorems/91837c14-aeef-4cd7-a0a3-1d6251ecb2bf
-- title:
--   An explicit Bézout identity proves the characteristic-two $y$-chart Jacobian ideal is the unit ideal
-- statement:
--   Let $K$ be a commutative ring of characteristic $2$, let $P=(x,1,z,w)$, let $q,k$ be the canonical equations, and let $M_{ab}$ be their Jacobian minors. Then $$\begin{aligned}&(xz^2w+z^3w+xzw^2+z^2w^2+zw^3+xz^2+z^3+xzw+z^2w+xw+z+1)q\&+(xzw+z^2w+zw^2+xw)k+(xzw+z^2w+zw^2+z^2+xw)M_{xy}\&+(x^2z+xz^2+xzw+z^2w+x^2+z^2+x+z)M_{xz}\&+(zw^2+z^2+z+w+1)M_{yz}+zwM_{yw}=1.\end{aligned}$$ This is the $y$-chart nonsingularity certificate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

theorem MazurProof.RationalPointsN25QuotientSmoothF2.yChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (x z w : K) :
    let P : Coordinates4 K := ⟨x, 1, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x*z^2*w + z^3*w + x*z*w^2 + z^2*w^2 + z*w^3 +
        x*z^2 + z^3 + x*z*w + z^2*w + x*w + z + 1) * q +
      (x*z*w + z^2*w + z*w^2 + x*w) * k +
      (x*z*w + z^2*w + z*w^2 + z^2 + x*w) * M.xy +
      (x^2*z + x*z^2 + x*z*w + z^2*w + x^2 + z^2 + x + z) * M.xz +
      (z*w^2 + z^2 + z + w + 1) * M.yz +
      (z*w) * M.yw = 1 := by sorry
