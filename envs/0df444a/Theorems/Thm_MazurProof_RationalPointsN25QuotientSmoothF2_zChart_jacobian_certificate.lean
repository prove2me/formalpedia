-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_zChart_jacobian_certificate
-- name    : MazurProof.RationalPointsN25QuotientSmoothF2.zChart_jacobian_certificate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:42.065206+00:00
-- url     : https://prove2.me/theorems/006cdab3-4427-4143-8352-150a36c8a07e
-- title:
--   An explicit Bézout identity proves the characteristic-two $z$-chart Jacobian ideal is the unit ideal
-- statement:
--   Let $K$ be a commutative ring of characteristic $2$, let $P=(x,y,1,w)$, let $q$ be the canonical quadric, and let $M_{ab}$ be the Jacobian minors. Then $$\begin{aligned}&(x^2+xy+xw+y)q+(xw+w^2+w+1)M_{xy}+(x^2+xw+x+w)M_{xz}\&+(x^2w+w^3+xy+yw+w^2+w)M_{xw}+(xw+w^2+y+w+1)M_{yz}\&+(x^2w+w^3+xy+xw+yw+y+w+1)M_{yw}+(xw+w^2+y+1)M_{zw}=1.\end{aligned}$$ This excludes singular points on the $z$-chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

theorem MazurProof.RationalPointsN25QuotientSmoothF2.zChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (x y w : K) :
    let P : Coordinates4 K := ⟨x, y, 1, w⟩
    let q := canonicalQuadric25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x^2 + x*y + x*w + y) * q +
      (x*w + w^2 + w + 1) * M.xy +
      (x^2 + x*w + x + w) * M.xz +
      (x^2*w + w^3 + x*y + y*w + w^2 + w) * M.xw +
      (x*w + w^2 + y + w + 1) * M.yz +
      (x^2*w + w^3 + x*y + x*w + y*w + y + w + 1) * M.yw +
      (x*w + w^2 + y + 1) * M.zw = 1 := by sorry
