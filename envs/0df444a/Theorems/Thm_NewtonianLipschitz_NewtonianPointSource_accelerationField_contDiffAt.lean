-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_contDiffAt
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_contDiffAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:22:26.107084+00:00
-- url     : https://prove2.me/theorems/b216e867-5fd5-4699-8aa6-43b936b7602e
-- title:
--   Newtonian Point Source: acceleration Field cont Diff At
-- statement:
--   The exact source field, not merely its candidate tidal tensor,
--   is C¹ at every nonzero source separation by transporting
--   Euclidean regularity to the actual Cartesian source field.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L63-L92
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L63-L92

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_contDiffAt
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 c.accelerationField x := by sorry
