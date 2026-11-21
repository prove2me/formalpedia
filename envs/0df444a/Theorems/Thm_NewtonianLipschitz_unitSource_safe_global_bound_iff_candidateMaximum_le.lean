-- Prove2me | Theorems.Thm_NewtonianLipschitz_unitSource_safe_global_bound_iff_candidateMaximum_le
-- name    : NewtonianLipschitz.unitSource_safe_global_bound_iff_candidateMaximum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:54:26.467599+00:00
-- url     : https://prove2.me/theorems/cb09a026-cbb8-4634-ae26-9d10e137f870
-- title:
--   Newtonian Lipschitz: unit Source safe global bound iff candidate Maximum le
-- statement:
--   Exact global optimality for one unit Newtonian source.
--   A real coefficient K controls every pair of unit-cube-safe endpoints
--   if and only if K is at least the exact coefficient C3.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/UnconditionalFiniteSource.lean#L27-L49
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/UnconditionalFiniteSource.lean#L27-L49

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Definitions.Def_NewtonianLipschitz_UnconditionalFiniteSource
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.unitSource_safe_global_bound_iff_candidateMaximum_le
    (K : ℝ) :
    (∀ x y : Vec3,
      (1 : ℝ) ≤ ‖x‖ →
      (1 : ℝ) ≤ ‖y‖ →
      ‖NewtonianPointSource.unitAxis.accelerationField x -
        NewtonianPointSource.unitAxis.accelerationField y‖ ≤
          K * ‖x - y‖) ↔ candidateMaximum ≤ K := by sorry
