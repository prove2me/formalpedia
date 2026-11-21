-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_inverse_fifth_derivative_coefficient_le
-- name    : NewtonianLipschitz.NewtonianPointSource.inverse_fifth_derivative_coefficient_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:30.920164+00:00
-- url     : https://prove2.me/theorems/791321cb-f77d-4592-8181-9f65d6efb3e1
-- title:
--   Newtonian Point Source: inverse fifth derivative coefficient le
-- statement:
--   The actual directional derivative of the exact field contains
--   a second inverse-fifth coefficient `3μ/r⁵`; the same positive
--   clearance bounds it by `3M/d⁵`.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L52-L66
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L52-L66

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.inverse_fifth_derivative_coefficient_le
    (c : NewtonianPointSource) (x : Vec3) (d M : ℝ)
    (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    3 * c.gravitationalParameter / euclideanRadius x ^ 5 ≤
      3 * M / d ^ 5 := by sorry
