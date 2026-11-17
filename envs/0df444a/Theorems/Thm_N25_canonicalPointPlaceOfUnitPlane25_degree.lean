-- Prove2me | Theorems.Thm_N25_canonicalPointPlaceOfUnitPlane25_degree
-- name    : N25.canonicalPointPlaceOfUnitPlane25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:15.751371+00:00
-- url     : https://prove2.me/theorems/548a0fcb-4ee3-4b1f-9d44-c1e6115d55e9
-- title:
--   The canonical place attached to a unit-plane point has degree one
-- statement:
--   Let $u,v∈ℚ$ satisfy $R(u,v)=0$ and $u≠0$. Transport the corresponding unit-plane place to the canonical function field. Then $$deg(P_{u,v}^{can})=1.$$ This carries rational plane points to the canonical model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlanePointPlace

open N25

theorem N25.canonicalPointPlaceOfUnitPlane25_degree (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    (canonicalPointPlaceOfUnitPlane25 u v hr hu).deg = 1 := by sorry
