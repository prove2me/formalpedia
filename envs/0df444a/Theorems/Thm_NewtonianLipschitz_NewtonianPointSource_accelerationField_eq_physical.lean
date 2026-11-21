-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_physical
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:30.997414+00:00
-- url     : https://prove2.me/theorems/03e1438f-e9c2-443b-9605-862d8a710194
-- title:
--   Newtonian Point Source: acceleration Field eq physical
-- statement:
--   The Newtonian Point Source construction uses the acceleration Field eq physical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L49-L58
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L49-L58

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_physical
    (c : NewtonianPointSource) (x : Vec3) :
    c.accelerationField x =
      WithLp.ofLp
        (physicalNewtonianAcceleration c.gravitationalParameter
          (toPhysicalVec3 x)) := by sorry
