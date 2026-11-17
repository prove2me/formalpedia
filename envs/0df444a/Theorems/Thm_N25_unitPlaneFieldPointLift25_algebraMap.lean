-- Prove2me | Theorems.Thm_N25_unitPlaneFieldPointLift25_algebraMap
-- name    : N25.unitPlaneFieldPointLift25_algebraMap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:45.419481+00:00
-- url     : https://prove2.me/theorems/27145a2a-a44e-4551-9542-61348f61a8a6
-- title:
--   The fraction-field lift agrees with affine evaluation
-- statement:
--   Let $F/ℚ$ be a field extension, let $R(u,v)=0$, and assume $u$ is transcendental over $ℚ$. For the induced field map $Ev_{u,v}:Frac(A)→F$ and every $a∈A$, $$Ev_{u,v}(a)=ev_{u,v}(a).$$ This connects ring and function-field evaluation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointLift

open N25

theorem N25.unitPlaneFieldPointLift25_algebraMap {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental ℚ u) (a : UnitPlaneRing) :
    unitPlaneFieldPointLift25 u v hr hu (algebraMap UnitPlaneRing UnitPlaneFF25 a) =
      unitPlaneFieldPointEvaluation25 u v hr a := by sorry
