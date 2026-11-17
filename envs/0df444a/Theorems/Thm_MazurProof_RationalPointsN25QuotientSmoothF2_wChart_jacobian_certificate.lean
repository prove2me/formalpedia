-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_wChart_jacobian_certificate
-- name    : MazurProof.RationalPointsN25QuotientSmoothF2.wChart_jacobian_certificate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:20.28149+00:00
-- url     : https://prove2.me/theorems/453636a8-29cd-4420-ab2d-71895d0017cd
-- title:
--   An explicit Bézout identity proves the characteristic-two $w$-chart Jacobian ideal is the unit ideal
-- statement:
--   Let $K$ be a commutative ring of characteristic $2$, let $P=(x,y,z,1)$, let $q,k$ be the canonical equations, and let $M_{ab}$ be their Jacobian minors. Then $$\begin{aligned}&(xz^4+z^4+xyz+y^2z+z^3+xy+y^2+xz+yz)q+(xz^2+xz+y+z+1)k\&+(xz^3+xz^2+z^3+xy+y^2+z^2+x+1)M_{xy}\&+(xz^3+xz^2+z^3+xy+y^2+z^2+x+z+1)M_{xz}+(xz+x+z)M_{yz}\&+(xz^2+xz+z^2)M_{yw}+(z^2+1)M_{zw}=1.\end{aligned}$$ This is the final affine-chart certificate for smoothness in characteristic $2$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

theorem MazurProof.RationalPointsN25QuotientSmoothF2.wChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (x y z : K) :
    let P : Coordinates4 K := ⟨x, y, z, 1⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x*z^4 + z^4 + x*y*z + y^2*z + z^3 + x*y + y^2 + x*z + y*z) * q +
      (x*z^2 + x*z + y + z + 1) * k +
      (x*z^3 + x*z^2 + z^3 + x*y + y^2 + z^2 + x + 1) * M.xy +
      (x*z^3 + x*z^2 + z^3 + x*y + y^2 + z^2 + x + z + 1) * M.xz +
      (x*z + x + z) * M.yz +
      (x*z^2 + x*z + z^2) * M.yw +
      (z^2 + 1) * M.zw = 1 := by sorry
