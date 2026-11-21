-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_length_mul_global
-- name    : NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:02:13.210056+00:00
-- url     : https://prove2.me/theorems/c8e23b87-6d6c-4125-bef4-6aa0d959a11f
-- title:
--   Newtonian Point Source: finite Differential Acceleration norm le length mul global
-- statement:
--   Unconditional finite-source N*M*C3/d³ inequality for the
--   true sum of Newtonian differential accelerations, without an
--   extra global one-source hypothesis. M bounds each actual source
--   gravitational parameter at the observation time.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/UnconditionalFiniteSource.lean#L72-L84
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/UnconditionalFiniteSource.lean#L72-L84

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
public import Definitions.Def_NewtonianLipschitz_UnconditionalFiniteSource
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_global
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d M : ℝ) (hd : 0 < d)
    (hsafe : ∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖)
    (hcap : ∀ source ∈ sources,
      (source t).gravitationalParameter ≤ M) :
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        (((sources.length : ℝ) * M) * candidateMaximum)) * ‖q‖ := by sorry
