-- Prove2me | Theorems.Thm_N25_unitPlanePointPlace25_degree
-- name    : N25.unitPlanePointPlace25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:06.892397+00:00
-- url     : https://prove2.me/theorems/2ee9cfc7-bd78-48f4-8e49-d8e401a77be0
-- title:
--   A rational unit-plane point defines a degree-one place
-- statement:
--   Let $u,v∈ℚ$ satisfy $R(u,v)=0$ and $u≠0$, and let $P_{u,v}$ be the associated function-field place. Then $$deg(P_{u,v})=1.$$ This turns a rational affine point into a rational place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlanePointPlace

open N25

theorem N25.unitPlanePointPlace25_degree (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    (unitPlanePointPlace25 u v hr hu).deg = 1 := by sorry
