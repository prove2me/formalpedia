-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_4_3
-- name    : MultiRegCournot.Equilibrium.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:41.905803+00:00
-- url     : https://prove2.me/theorems/fc80216f-121c-41ca-87a8-781b7d105d3b
-- title:
--   Lemma 4.3, p. 12 — Φ has a unique fixed point
-- statement:
--   The reduced-form best-response operator Φ has exactly one fixed point ρ* in the marginal-profit box.
--
--   $$\exists!\rho^*\in[0,\bar w]^N:\quad\Phi(\rho^*)=\rho^*.$$
--
--   This identifies the marginal-profit vector used in the unique-equilibrium theorem.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 12, Lemma 4.3

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma 4.3, p. 12. -/
theorem lemma_4_3 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∃! rho : Fin N → ℝ, rho ∈ M.box ∧ M.Phi rho = rho := by sorry

end MultiRegCournot.Equilibrium
