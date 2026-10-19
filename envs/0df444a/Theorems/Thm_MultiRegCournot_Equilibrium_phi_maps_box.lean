-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_phi_maps_box
-- name    : MultiRegCournot.Equilibrium.phi_maps_box
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:55.281417+00:00
-- url     : https://prove2.me/theorems/3ae468ba-61ce-4421-910a-24f970f2897e
-- title:
--   Appendix C, p. 35 display — Φ maps the vector box into itself
-- statement:
--   Let w̄ be the largest reservation price. The reduced-form best-response operator Φ sends every marginal-profit vector in [0,w̄]ᴺ to another vector in the same box.
--
--   $$\Phi([0,\bar w]^N)\subseteq[0,\bar w]^N.$$
--
--   This gives Φ the bounded domain used in the fixed-point results.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs. Φ is computed from Q̂ and capacity; its inverse branch is an infimum of the exact capacity level set.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 35, Appendix C display before Lemma C.5

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Appendix C, p. 35 display. -/
theorem phi_maps_box {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∀ rho ∈ M.box, M.Phi rho ∈ M.box := by sorry

end MultiRegCournot.Equilibrium
