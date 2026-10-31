-- Prove2me | Theorems.Thm_MCAEndToEndMission_concentration_connectivity
-- name    : MCAEndToEndMission.concentration_connectivity
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T16:15:49.90405+00:00
-- url     : https://prove2.me/theorems/0eda09a3-49ed-4f02-b91f-0cd2ee160050
-- title:
--   Concentration connectivity theorem
-- statement:
--   For a differentiable steady-state metabolic network with a left-invertible linearized stoichiometric operator and nonzero normalization factors, the concentration-control matrix multiplied by the elasticity matrix equals the negative identity. This is the main concentration connectivity theorem.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Sections 2-3, https://arxiv.org/abs/2501.12519

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

namespace MCAEndToEndMission
noncomputable section
theorem concentration_connectivity
    {n m : ℕ}
    (f : Fin n → (Fin m → ℝ) → ℝ)
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (N : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin n → ℝ)
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q, N.mulVec (fun k => MCAEndToEnd.rate f s q k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * MCAEndToEnd.elasticityDerivative f s p) = 1)
    (hp : ∀ k, p k ≠ 0)
    (hf0 : ∀ k, f k (s p) ≠ 0)
    (hs0 : ∀ i, s p i ≠ 0) :
    MCAEndToEnd.concentrationControl s p * MCAEndToEnd.elasticity f s p = -1 := by sorry
end
end MCAEndToEndMission
