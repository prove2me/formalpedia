-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_theorem_4_5
-- name    : MultiRegCournot.Equilibrium.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:42.749373+00:00
-- url     : https://prove2.me/theorems/934b2d7d-9d20-4cf1-97df-6a169c049641
-- title:
--   Theorem 4.5, p. 12 — the unique equilibrium is Q̂(ρ*)
-- statement:
--   There is a unique fixed point ρ* of Φ in [0,w̄]ᴺ. A quantity profile Q is a Nash equilibrium of the original capacity-constrained game if and only if Q is the allocation Q̂(ρ*).
--
--   $$\exists!\rho^*\in[0,\bar w]^N:\quad\Phi(\rho^*)=\rho^*,\qquad Q\text{ is an equilibrium}\Longleftrightarrow Q=\hat Q(\rho^*).$$
--
--   Thus the original game has exactly one equilibrium allocation, identified by its fixed-point marginal-profit vector.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs. The equivalence uses the full feasible unilateral-deviation definition of Nash equilibrium; neither Φ nor ρ* is a free assumption.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 12, Theorem 4.5

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Theorem 4.5, p. 12: existence and uniqueness of both the fixed point and equilibrium. -/
theorem theorem_4_5 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∃ rhos ∈ M.box, M.Phi rhos = rhos ∧
      (∀ rho ∈ M.box, M.Phi rho = rho → rho = rhos) ∧
      ∀ Q : Fin N → Fin R → ℝ, M.IsEquilibrium Q ↔ Q = M.Qhat rhos := by sorry

end MultiRegCournot.Equilibrium
