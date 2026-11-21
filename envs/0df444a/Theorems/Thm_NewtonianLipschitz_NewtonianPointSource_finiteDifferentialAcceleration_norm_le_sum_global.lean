-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_sum_global
-- name    : NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_sum_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:02:58.57707+00:00
-- url     : https://prove2.me/theorems/a237c909-42dc-4d3f-8fe7-146ad4cea8df
-- title:
--   Newtonian Point Source: finite Differential Acceleration norm le sum global
-- statement:
--   Unconditional finite-source bound using the SUM of actual
--   nonnegative gravitational parameters at time t. The source
--   accelerations are exact nonlinear force differences.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/UnconditionalFiniteSource.lean#L54-L66
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/UnconditionalFiniteSource.lean#L54-L66

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Definitions.Def_NewtonianLipschitz_UnconditionalFiniteSource
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_sum_global
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d : ℝ) (hd : 0 < d)
    (hsafe : ∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖) :
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        ((sources.map (fun source =>
          (source t).gravitationalParameter)).sum * candidateMaximum)) *
        ‖q‖ := by sorry
