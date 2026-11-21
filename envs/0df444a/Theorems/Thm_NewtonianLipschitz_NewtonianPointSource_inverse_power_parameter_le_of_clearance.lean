-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_power_parameter_le_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.inverse_power_parameter_le_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:24.397831+00:00
-- url     : https://prove2.me/theorems/8f37f576-738c-48cc-a214-63604145817f
-- title:
--   Newtonian Point Source: inverse power parameter le of clearance
-- statement:
--   The Newtonian Point Source construction uses the inverse power parameter le of clearance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L20-L36
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L20-L36

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.inverse_power_parameter_le_of_clearance
    (c : NewtonianPointSource) (x : Vec3) (d M : ℝ) (n : ℕ)
    (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    c.gravitationalParameter / euclideanRadius x ^ n ≤
      M / d ^ n := by sorry
