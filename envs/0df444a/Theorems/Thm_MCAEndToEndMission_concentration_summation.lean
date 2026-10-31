-- Prove2me | Theorems.Thm_MCAEndToEndMission_concentration_summation
-- name    : MCAEndToEndMission.concentration_summation
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T16:13:50.525268+00:00
-- url     : https://prove2.me/theorems/408fb1db-2df4-406e-ac51-3605cdadd007
-- title:
--   Concentration summation theorem
-- statement:
--   If the steady-state concentration map is homogeneous of degree zero under positive rescaling of all enzyme parameters and concentrations are nonzero, then the normalized concentration-control coefficients in every concentration row sum to zero.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Sections 2-3, https://arxiv.org/abs/2501.12519

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

namespace MCAEndToEndMission
noncomputable section
theorem concentration_summation
    {n m : ℕ}
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (p : Fin n → ℝ)
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p)
    (hs0 : ∀ i, s p i ≠ 0) :
    ∀ i, ∑ l, MCAEndToEnd.concentrationControl s p i l = 0 := by sorry
end
end MCAEndToEndMission
