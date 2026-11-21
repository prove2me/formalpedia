-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_safe_distinct_secant_pairs
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_distinct_secant_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:43:12.75263+00:00
-- url     : https://prove2.me/theorems/8ff56dc6-db9e-4b61-a89f-941608cb1f81
-- title:
--   Newtonian Point Source: unit Axis exists safe distinct secant pairs
-- statement:
--   There is a unit Cartesian derivative-attaining direction
--   for which every positive outward perturbation is a distinct
--   admissible point, exactly the step length away from the
--   critical unit-clearance displacement.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L41-L88
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L41-L88

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_distinct_secant_pairs :
    ∃ h : Vec3, ‖h‖ = 1 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum ∧
      ∀ s : ℝ, 0 < s →
        (1 : ℝ) ≤
          ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h‖ ∧
        ‖(normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h) -
          normalizedVector candidateCriticalPoint candidateCriticalPoint‖ =
            s ∧
        normalizedVector candidateCriticalPoint candidateCriticalPoint +
          s • h ≠
            normalizedVector candidateCriticalPoint candidateCriticalPoint := by sorry
