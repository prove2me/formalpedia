-- Prove2me | Theorems.Thm_MCAEndToEndMission_flux_summation
-- name    : MCAEndToEndMission.flux_summation
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T16:14:28.703058+00:00
-- url     : https://prove2.me/theorems/154773e2-e0fa-49cf-a20b-ac5faffb1f84
-- title:
--   Flux summation theorem
-- statement:
--   For a differentiable rate and steady-state model whose concentration map is homogeneous of degree zero, each nonzero linear flux has normalized flux-control coefficients summing to one across all enzyme parameters.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Sections 2-3, https://arxiv.org/abs/2501.12519

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

namespace MCAEndToEndMission
noncomputable section
theorem flux_summation
    {n m q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → (Fin m → ℝ) → ℝ)
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (p : Fin n → ℝ)
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p)
    (hJ0 : ∀ r, MCAEndToEnd.flux R f s p r ≠ 0) :
    ∀ r, ∑ l, MCAEndToEnd.fluxControl R f s p r l = 1 := by sorry
end
end MCAEndToEndMission
