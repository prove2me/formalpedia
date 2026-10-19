-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_4_4
-- name    : MultiRegCournot.Equilibrium.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:52.60263+00:00
-- url     : https://prove2.me/theorems/c063cf6a-8f44-40bb-b397-da04e8a3d636
-- title:
--   Lemma 4.4, p. 12 — equilibrium marginal profits are fixed by Φ
-- statement:
--   Let Q be a Nash equilibrium and let ρ be its associated vector of nonnegative marginal profits from Lemma 4.1, assigning zero to a firm with zero output. If Q satisfies condition (2) with ρ, then ρ lies in the marginal-profit box and is a fixed point of Φ.
--
--   $$\rho\in[0,\bar w]^N,\qquad\Phi(\rho)=\rho.$$
--
--   The result connects equilibria of the quantity game to fixed points of the reduced-form operator. Equality Q=Q̂(ρ) is obtained from Proposition 4.2 and is not an extra hypothesis.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 12, Lemma 4.4

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma 4.4, p. 12: the marginal-profit vector of an equilibrium is fixed by Φ. -/
theorem lemma_4_4 {N R : ℕ} (M : Market N R) (hM : M.Standing)
    (Q : Fin N → Fin R → ℝ) (rho : Fin N → ℝ)
    (hQ : M.IsEquilibrium Q) (hrho : ∀ i, 0 ≤ rho i)
    (hzero : ∀ i, qTotFirm Q i = 0 → rho i = 0)
    (hcond : ∀ i, M.Cond2 Q i (rho i)) :
    rho ∈ M.box ∧ M.Phi rho = rho := by sorry

end MultiRegCournot.Equilibrium
