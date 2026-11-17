-- Prove2me | Theorems.Thm_N25_unitPlaneFieldPointLift25C_coordinates
-- name    : N25.unitPlaneFieldPointLift25C_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:18.245442+00:00
-- url     : https://prove2.me/theorems/ec217104-830a-42c7-8298-0fc9ad1ba3dc
-- title:
--   The general function-field lift preserves both plane coordinates
-- statement:
--   Under the same hypotheses over $K⊆F$, $$Ev_{u,v}(U)=u ∧ Ev_{u,v}(V)=v.$$ This supplies the coordinate formula in arbitrary characteristic.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField

open N25

theorem N25.unitPlaneFieldPointLift25C_coordinates
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental K u) :
    unitPlaneFieldPointLift25C (K := K) u v hr hu
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneFF25C K) (unitPlaneU25C K)) = u ∧
    unitPlaneFieldPointLift25C (K := K) u v hr hu
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneFF25C K) (unitPlaneV25C K)) = v := by sorry
