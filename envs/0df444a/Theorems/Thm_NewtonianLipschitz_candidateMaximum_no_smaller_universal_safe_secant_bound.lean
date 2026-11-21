-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_no_smaller_universal_safe_secant_bound
-- name    : NewtonianLipschitz.candidateMaximum_no_smaller_universal_safe_secant_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:56:04.957662+00:00
-- url     : https://prove2.me/theorems/fe5aa104-285f-4aaa-884a-63ceefafc2ff
-- title:
--   Newtonian Lipschitz: candidate Maximum no smaller universal safe secant bound
-- statement:
--   No strictly smaller constant can hold for all *admissible*
--   two-point finite differences, already for a single unit source.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L205-L215
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/AdmissibleSecantPairs.lean#L205-L215

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_no_smaller_universal_safe_secant_bound
    (K : ℝ) (hK : K < candidateMaximum) :
    ¬ ∀ x y : Vec3,
      (1 : ℝ) ≤ ‖x‖ → (1 : ℝ) ≤ ‖y‖ →
        ‖NewtonianPointSource.unitAxis.accelerationField x -
          NewtonianPointSource.unitAxis.accelerationField y‖ ≤
            K * ‖x - y‖ := by sorry
