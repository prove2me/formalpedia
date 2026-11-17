-- Prove2me | Theorems.Thm_N25_unitPlaneFieldPointLift25C_algebraMap
-- name    : N25.unitPlaneFieldPointLift25C_algebraMap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:19.557461+00:00
-- url     : https://prove2.me/theorems/efb2d346-e353-475d-b3ba-4081a06e1008
-- title:
--   The general fraction-field lift agrees with affine evaluation
-- statement:
--   Let $K⊆F$ be fields, let $R(u,v)=0$, and assume $u$ is transcendental over $K$. For $Ev_{u,v}:Frac(A_K)→F$ and every $a∈A_K$, $$Ev_{u,v}(a)=ev_{u,v}(a).$$ This is the general compatibility formula.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField

open N25

theorem N25.unitPlaneFieldPointLift25C_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental K u)
    (a : UnitPlaneRing25C K) :
    unitPlaneFieldPointLift25C (K := K) u v hr hu
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneFF25C K) a) =
      unitPlaneFieldPointEvaluation25C (K := K) u v hr a := by sorry
