-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_proposition_4_2
-- name    : MultiRegCournot.Equilibrium.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:41.024973+00:00
-- url     : https://prove2.me/theorems/cf609ada-a1e6-48a3-82f4-1f82ae9c3393
-- title:
--   Proposition 4.2, p. 9 — unique allocation for each marginal-profit vector (existence and uniqueness only)
-- statement:
--   For every vector ρ in [0,w̄]ᴺ, there is exactly one nonnegative allocation Q for which every firm satisfies condition (2) with marginal profit ρⁱ.
--
--   $$\forall\rho\in[0,\bar w]^N,\quad\exists!Q\ge0:\quad g_r^i(Q)\le\rho^i,\;q_r^i(g_r^i(Q)-\rho^i)=0\quad(\forall i,r).$$
--
--   This makes Q̂(ρ) a well-defined allocation on the box. The printed proposition also asserts finite termination of Algorithm 4.1; this item formalizes only its existence and uniqueness clause.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 9, Proposition 4.2

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Proposition 4.2, p. 9: existence and uniqueness, excluding Algorithm 4.1. -/
theorem proposition_4_2 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∀ rho ∈ M.box, ∃! Q : Fin N → Fin R → ℝ,
      (∀ i r, 0 ≤ Q i r) ∧ ∀ i, M.Cond2 Q i (rho i) := by sorry

end MultiRegCournot.Equilibrium
