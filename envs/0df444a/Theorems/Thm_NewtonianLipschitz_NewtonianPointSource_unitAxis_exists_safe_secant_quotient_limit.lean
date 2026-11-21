-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_safe_secant_quotient_limit
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_secant_quotient_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:42:20.031403+00:00
-- url     : https://prove2.me/theorems/1100b570-99d2-4c4a-bbcc-cd6cadf2e61b
-- title:
--   Newtonian Point Source: unit Axis exists safe secant quotient limit
-- statement:
--   R036: the actual finite-difference quotients along an admissible
--   outward unit ray converge to the sharp Newtonian coefficient.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L102-L155
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L102-L155

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_secant_quotient_limit :
    ∃ h : Vec3, ‖h‖ = 1 ∧
      (∀ s : ℝ, 0 < s →
        (1 : ℝ) ≤
          ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h‖ ∧
        ‖(normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h) -
          normalizedVector candidateCriticalPoint candidateCriticalPoint‖ =
            s ∧
        normalizedVector candidateCriticalPoint candidateCriticalPoint +
          s • h ≠
            normalizedVector candidateCriticalPoint candidateCriticalPoint) ∧
      Filter.Tendsto
        (fun s : ℝ =>
          ‖s⁻¹ •
            (NewtonianPointSource.unitAxis.accelerationField
                (normalizedVector candidateCriticalPoint candidateCriticalPoint +
                  s • h) -
              NewtonianPointSource.unitAxis.accelerationField
                (normalizedVector candidateCriticalPoint candidateCriticalPoint))‖)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds candidateMaximum) := by sorry
