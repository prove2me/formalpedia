-- Prove2me | Theorems.Thm_NewtonianLipschitz_tangential_normalized_first_numerator_le_radius
-- name    : NewtonianLipschitz.tangential_normalized_first_numerator_le_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:50:57.830689+00:00
-- url     : https://prove2.me/theorems/de452a76-607b-4143-a18c-ae6dc29eecad
-- title:
--   Newtonian Lipschitz: tangential normalized first numerator le radius
-- statement:
--   The first restricted Jacobian-row numerator is bounded
--   by 5/4 times the TRUE Euclidean radius to the fifth power.
--   This is the nonnegative square-root step left implicit in R042.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L54-L91
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L54-L91

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.tangential_normalized_first_numerator_le_radius
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    3 * (u + v) ≤
      (5 / 4 : ℝ) * euclideanRadius (normalizedVector u v) ^ 5 := by sorry
