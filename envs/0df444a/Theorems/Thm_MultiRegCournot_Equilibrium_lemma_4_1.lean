-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_4_1
-- name    : MultiRegCournot.Equilibrium.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:48.414864+00:00
-- url     : https://prove2.me/theorems/bfc3e595-2071-4b58-8787-e52edf5373b9
-- title:
--   Lemma 4.1, p. 9 — marginal-profit conditions at equilibrium
-- statement:
--   Fix a Nash equilibrium Q. Every firm i with positive total production has a unique nonnegative marginal profit ρⁱ such that, in each region r, its marginal profit gⁱᵣ is at most ρⁱ and qⁱᵣ(gⁱᵣ−ρⁱ)=0. For a firm with zero production, the same conditions hold with ρⁱ=0.
--
--   $$g_r^i(Q)\le\rho^i,\qquad q_r^i(g_r^i(Q)-\rho^i)=0.$$
--
--   This associates a marginal-profit vector with each equilibrium.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 9, Lemma 4.1, (2)

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma 4.1, p. 9, including the convention for a non-producing firm. -/
theorem lemma_4_1 {N R : ℕ} (M : Market N R) (hM : M.Standing)
    (Q : Fin N → Fin R → ℝ) (hQ : M.IsEquilibrium Q) :
    (∀ i, 0 < qTotFirm Q i → ∃! rhoi : ℝ, 0 ≤ rhoi ∧ M.Cond2 Q i rhoi) ∧
      ∀ i, qTotFirm Q i = 0 → M.Cond2 Q i 0 := by sorry

end MultiRegCournot.Equilibrium
