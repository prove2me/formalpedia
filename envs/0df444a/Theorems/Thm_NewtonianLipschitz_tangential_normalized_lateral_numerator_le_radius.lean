-- Prove2me | Theorems.Thm_NewtonianLipschitz_tangential_normalized_lateral_numerator_le_radius
-- name    : NewtonianLipschitz.tangential_normalized_lateral_numerator_le_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:50:45.665806+00:00
-- url     : https://prove2.me/theorems/768f900b-d545-4888-9392-cccbd3e2555d
-- title:
--   Newtonian Lipschitz: tangential normalized lateral numerator le radius
-- statement:
--   The second or third restricted Jacobian-row numerator
--   is bounded by the fifth power of the true physical radius.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L95-L108
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L95-L108

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.tangential_normalized_lateral_numerator_le_radius
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v ≤
      (5 / 4 : ℝ) * euclideanRadius (normalizedVector u v) ^ 5 := by sorry
