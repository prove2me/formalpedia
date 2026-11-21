-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_safe_sharp_outward_ray
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_sharp_outward_ray
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:42:37.926712+00:00
-- url     : https://prove2.me/theorems/dbcdbc11-98ff-41af-bb97-76d26908f4ec
-- title:
--   Newtonian Point Source: unit Axis exists safe sharp outward ray
-- statement:
--   A derivative-attaining direction has an orientation
--   whose entire forward ray satisfies Cartesian unit clearance.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleCriticalDirection.lean#L68-L82
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleCriticalDirection.lean#L68-L82

module
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_sharp_outward_ray :
    ∃ h : Vec3, ‖h‖ ≤ 1 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum ∧
      ∀ s : ℝ, 0 ≤ s →
        (1 : ℝ) ≤
          ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h‖ := by sorry
