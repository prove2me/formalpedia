-- Prove2me | Theorems.Thm_NewtonianLipschitz_tangential_normalized_radius_bounds
-- name    : NewtonianLipschitz.tangential_normalized_radius_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:49:57.771286+00:00
-- url     : https://prove2.me/theorems/ba7b295a-245f-4199-8969-ebf1c0c466d4
-- title:
--   Newtonian Lipschitz: tangential normalized radius bounds
-- statement:
--   The exact physical Euclidean radius of (1,u,v) is at least
--   one, and its fifth power controls the square of (1+u²+v²).
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L26-L49
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/PhysicalTangentialNormalized.lean#L26-L49

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz

theorem NewtonianLipschitz.tangential_normalized_radius_bounds
    (u v : ℝ) :
    let r := euclideanRadius (normalizedVector u v)
    1 ≤ r ∧
      (1 + u ^ 2 + v ^ 2) ^ 2 ≤ r ^ 5 := by sorry
