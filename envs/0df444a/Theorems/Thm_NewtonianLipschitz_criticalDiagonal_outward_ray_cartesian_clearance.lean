-- Prove2me | Theorems.Thm_NewtonianLipschitz_criticalDiagonal_outward_ray_cartesian_clearance
-- name    : NewtonianLipschitz.criticalDiagonal_outward_ray_cartesian_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:41:55.880706+00:00
-- url     : https://prove2.me/theorems/b3c76dcd-ffff-4cc0-9a74-e56c1e569fcf
-- title:
--   Newtonian Lipschitz: critical Diagonal outward ray cartesian clearance
-- statement:
--   The critical diagonal remains outside the open
--   Cartesian safety cube under every nonnegative outward
--   perturbation of the first coordinate.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleCriticalDirection.lean#L46-L64
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleCriticalDirection.lean#L46-L64

module
public import Definitions.Def_NewtonianLipschitz_DerivativeAttainingDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.criticalDiagonal_outward_ray_cartesian_clearance
    (h : Vec3) (hfirst : 0 ≤ h 0)
    (s : ℝ) (hs : 0 ≤ s) :
    (1 : ℝ) ≤
      ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
        s • h‖ := by sorry
