-- Prove2me | Theorems.Thm_NewtonianLipschitz_tangential_lateral_row_le_five_four_quadratic
-- name    : NewtonianLipschitz.tangential_lateral_row_le_five_four_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:48:10.953966+00:00
-- url     : https://prove2.me/theorems/d9076dc2-a1dc-4baa-99e0-cb09e4b76552
-- title:
--   Newtonian Lipschitz: tangential lateral row le five four quadratic
-- statement:
--   Each lateral tangential row numerator obeys a simpler
--   quadratic bound, with no restriction u,v ≤ 1.
--   This is the second scalar ingredient for a 5/4 safe-plane
--   derivative estimate.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L66-L96
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L66-L96

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.tangential_lateral_row_le_five_four_quadratic
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v ≤
      (5 / 4 : ℝ) * (1 + u ^ 2 + v ^ 2) ^ 2 := by sorry
