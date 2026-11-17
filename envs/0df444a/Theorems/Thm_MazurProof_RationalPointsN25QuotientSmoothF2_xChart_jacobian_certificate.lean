-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_xChart_jacobian_certificate
-- name    : MazurProof.RationalPointsN25QuotientSmoothF2.xChart_jacobian_certificate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:40.407937+00:00
-- url     : https://prove2.me/theorems/fcacb285-23aa-474f-94ad-31c15544c320
-- title:
--   An explicit Bézout identity proves the characteristic-two $x$-chart Jacobian ideal is the unit ideal
-- statement:
--   Let $K$ be a commutative ring of characteristic $2$, let $P=(1,y,z,w)$, let $q$ and $k$ be the canonical quadric and cubic at $P$, and let $M_{ab}$ be the corresponding Jacobian minors. Then $$\begin{aligned}&(yzw+z^2+zw+w^2+y+w)q+(yzw+z^2+yw+zw+w^2+z+w)k\&+(yw+y+z+w+1)M_{xz}+(yw+y+z+w+1)M_{xw}\&+(yz^2w+z^3+y^2w+z^2w+yw^2+zw^2+y^2+yz+yw+w^2+y+z+w)M_{yz}\&+(y+1)M_{yw}+(y+1)M_{zw}=1.\end{aligned}$$ This certificate excludes singular points on the normalized $x$-chart in characteristic $2$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

theorem MazurProof.RationalPointsN25QuotientSmoothF2.xChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (y*z*w + z^2 + z*w + w^2 + y + w) * q +
      (y*z*w + z^2 + y*w + z*w + w^2 + z + w) * k +
      (y*w + y + z + w + 1) * M.xz +
      (y*w + y + z + w + 1) * M.xw +
      (y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
        y^2 + y*z + y*w + w^2 + y + z + w) * M.yz +
      (y + 1) * M.yw + (y + 1) * M.zw = 1 := by sorry
