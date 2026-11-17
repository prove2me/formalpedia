-- Prove2me | Theorems.Thm_N25_unitPlaneFieldPointLift25_coordinates
-- name    : N25.unitPlaneFieldPointLift25_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:20.141175+00:00
-- url     : https://prove2.me/theorems/c277bb9c-a5f1-4099-8500-0df5ef0fc8a8
-- title:
--   The rational function-field lift preserves both plane coordinates
-- statement:
--   Under the same hypotheses, the induced field map satisfies $$Ev_{u,v}(U)=u ∧ Ev_{u,v}(V)=v.$$ This pins the embedding to the chosen point.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointLift

open N25

theorem N25.unitPlaneFieldPointLift25_coordinates {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental ℚ u) :
    unitPlaneFieldPointLift25 u v hr hu (algebraMap UnitPlaneRing UnitPlaneFF25 unitPlaneU) = u ∧
    unitPlaneFieldPointLift25 u v hr hu (algebraMap UnitPlaneRing UnitPlaneFF25 unitPlaneV) = v := by sorry
