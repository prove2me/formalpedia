-- Prove2me | Theorems.Thm_NewtonianLipschitz_tangential_denominator_fifth_power_ge_twelve
-- name    : NewtonianLipschitz.tangential_denominator_fifth_power_ge_twelve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:48:09.880034+00:00
-- url     : https://prove2.me/theorems/4a3e0a72-de2d-458b-9918-c164478042ec
-- title:
--   Newtonian Lipschitz: tangential denominator fifth power ge twelve
-- statement:
--   An explicit sum-of-nonnegative-terms certificate for the
--   radial denominator inequality, valid without upper bounds on t.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L25-L39
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/TangentialAlgebra.lean#L25-L39

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.tangential_denominator_fifth_power_ge_twelve
    (t : ℝ) (ht : 0 ≤ t) :
    12 * t ≤ (1 + t) ^ 5 := by sorry
