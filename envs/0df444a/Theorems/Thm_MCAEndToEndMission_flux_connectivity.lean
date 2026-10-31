-- Prove2me | Theorems.Thm_MCAEndToEndMission_flux_connectivity
-- name    : MCAEndToEndMission.flux_connectivity
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T16:15:04.204108+00:00
-- url     : https://prove2.me/theorems/244eca0a-a303-42f7-aafa-c249992b9100
-- title:
--   Flux connectivity theorem
-- statement:
--   Under the differentiability, steady-state, inverse, and nondegeneracy assumptions of the metabolic control model, the elasticity-weighted sum of flux-control coefficients vanishes for every selected flux and concentration coordinate.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Sections 2-3, https://arxiv.org/abs/2501.12519

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

namespace MCAEndToEndMission
noncomputable section
theorem flux_connectivity
    {n m q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → (Fin m → ℝ) → ℝ)
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (N : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin n → ℝ)
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q', N.mulVec (fun k => MCAEndToEnd.rate f s q' k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * MCAEndToEnd.elasticityDerivative f s p) = 1)
    (hp : ∀ k, p k ≠ 0)
    (hf0 : ∀ k, f k (s p) ≠ 0)
    (hJ0 : ∀ r, MCAEndToEnd.flux R f s p r ≠ 0) :
    ∀ r j, ∑ l, MCAEndToEnd.fluxControl R f s p r l * MCAEndToEnd.elasticity f s p l j = 0 := by sorry
end
end MCAEndToEndMission
