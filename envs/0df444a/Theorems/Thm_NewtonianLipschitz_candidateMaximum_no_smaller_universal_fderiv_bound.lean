-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_no_smaller_universal_fderiv_bound
-- name    : NewtonianLipschitz.candidateMaximum_no_smaller_universal_fderiv_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:55:33.098127+00:00
-- url     : https://prove2.me/theorems/9460aec3-8a95-4835-889d-dc4977cd4d14
-- title:
--   Newtonian Lipschitz: candidate Maximum no smaller universal fderiv bound
-- statement:
--   A strictly smaller coefficient cannot bound the actual
--   Frechet operator norm for all nonzero source displacements.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/DerivativeCoefficientMinimality.lean#L57-L66
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/DerivativeCoefficientMinimality.lean#L57-L66

module
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
public import Definitions.Def_NewtonianLipschitz_DerivativeCoefficientMinimality
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_no_smaller_universal_fderiv_bound
    (K : ℝ) (hK : K < candidateMaximum) :
    ¬ ∀ (c : NewtonianPointSource) (x : Vec3),
        x ≠ 0 →
          ‖fderiv ℝ c.accelerationField x‖ ≤
            (1 / ‖x‖ ^ 3) * (c.gravitationalParameter * K) := by sorry
