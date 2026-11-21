-- Prove2me | Theorems.Thm_NewtonianLipschitz_tangential_first_row_squared_le_five_four
-- name    : NewtonianLipschitz.tangential_first_row_squared_le_five_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:48:19.685645+00:00
-- url     : https://prove2.me/theorems/60d46762-4a04-4653-b9c3-337a8c88a05d
-- title:
--   Newtonian Lipschitz: tangential first row squared le five four
-- statement:
--   The first tangential row numerator is below the 5/4
--   coefficient after squaring the positive radial denominator.
--   The variables u,v represent normalized absolute coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L44-L60
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L44-L60

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.tangential_first_row_squared_le_five_four
    (u v t : ℝ) (ht : t = u ^ 2 + v ^ 2) :
    (3 * (u + v)) ^ 2 ≤
      ((5 / 4 : ℝ) ^ 2) * (1 + t) ^ 5 := by sorry
