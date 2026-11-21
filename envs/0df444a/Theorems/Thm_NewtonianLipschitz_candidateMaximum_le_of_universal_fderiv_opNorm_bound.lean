-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_le_of_universal_fderiv_opNorm_bound
-- name    : NewtonianLipschitz.candidateMaximum_le_of_universal_fderiv_opNorm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:38:09.325562+00:00
-- url     : https://prove2.me/theorems/f0bc1796-40e0-4daa-a67e-dcbc42f317b7
-- title:
--   Newtonian Lipschitz: candidate Maximum le of universal fderiv op Norm bound
-- statement:
--   Any coefficient bounding every point-source Frechet
--   operator norm at nonzero Cartesian separation must be
--   at least the exact candidate maximum.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/DerivativeCoefficientMinimality.lean#L27-L53
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/DerivativeCoefficientMinimality.lean#L27-L53

module
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
public import Definitions.Def_NewtonianLipschitz_DerivativeCoefficientMinimality
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_le_of_universal_fderiv_opNorm_bound
    (K : ℝ)
    (hK : ∀ (c : NewtonianPointSource) (x : Vec3),
      x ≠ 0 →
        ‖fderiv ℝ c.accelerationField x‖ ≤
          (1 / ‖x‖ ^ 3) * (c.gravitationalParameter * K)) :
    candidateMaximum ≤ K := by sorry
