-- Prove2me | Theorems.Thm_N25_canonicalPointPlaceOfUnitPlane25_unit_orders
-- name    : N25.canonicalPointPlaceOfUnitPlane25_unit_orders
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:19.487226+00:00
-- url     : https://prove2.me/theorems/f510c177-12b5-4115-8daa-caf57b33fb64
-- title:
--   Both unit coordinates are units at a rational point of the unit plane
-- statement:
--   Let $u,v∈ℚ$ satisfy the unit-plane equation $R(u,v)=0$, and assume $u\ne0$ and $v\ne0$. Let $P_{u,v}$ be the associated place of the canonical function field, and let $U,V$ be the two canonical coordinate functions. Then $$\operatorname{ord}_{P_{u,v}}(U)=0,\qquad \operatorname{ord}_{P_{u,v}}(V)=0.$$ This shows that the place lies in the principal open where both modular-unit coordinates are invertible.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalFunctionCoordinates
import Definitions.Def_N25_CanonicalNoncuspPlace

open N25

theorem N25.canonicalPointPlaceOfUnitPlane25_unit_orders
    (u v : ℚ) (hr : planeRelation u v = 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    (canonicalPointPlaceOfUnitPlane25 u v hr hu).ord canonicalFunctionU25 = 0 ∧
      (canonicalPointPlaceOfUnitPlane25 u v hr hu).ord canonicalFunctionV25 = 0 := by sorry
