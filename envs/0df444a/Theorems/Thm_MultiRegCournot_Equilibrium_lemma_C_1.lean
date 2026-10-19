-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_C_1
-- name    : MultiRegCournot.Equilibrium.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:18.423357+00:00
-- url     : https://prove2.me/theorems/98cc7666-0707-484d-ba99-8d6c0573e01f
-- title:
--   Lemma C.1, p. 29 — a pure equilibrium exists
-- statement:
--   Under the standing market assumptions, there exists a feasible pure-strategy Nash equilibrium of the capacity-constrained quantity game.
--
--   $$\exists Q,\quad Q\text{ is a Nash equilibrium.}$$
--
--   This supplies existence of an equilibrium allocation for the main characterization.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 29, Lemma C.1

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma C.1, p. 29. -/
theorem lemma_C_1 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∃ Q : Fin N → Fin R → ℝ, M.IsEquilibrium Q := by sorry

end MultiRegCournot.Equilibrium
