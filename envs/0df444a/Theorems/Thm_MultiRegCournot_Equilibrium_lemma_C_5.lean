-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_C_5
-- name    : MultiRegCournot.Equilibrium.lemma_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:42.601709+00:00
-- url     : https://prove2.me/theorems/b34dbaa3-4b19-4193-b888-a8d2eb5c7595
-- title:
--   Lemma C.5, p. 35 — least and greatest fixed points (without convergence)
-- statement:
--   The operator Φ has a least fixed point ρ̲ and a greatest fixed point ρ̄ in [0,w̄]ᴺ. Every fixed point ρ in the box lies between them componentwise.
--
--   $$\Phi(\underline\rho)=\underline\rho,\quad\Phi(\overline\rho)=\overline\rho,\quad\underline\rho\le\rho\le\overline\rho.$$
--
--   This bounds the fixed points before their uniqueness is established. The printed lemma also states convergence of iterates from the box endpoints; that clause is outside this item.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 35, Lemma C.5

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma C.5, p. 35: least and greatest fixed points, excluding convergence. -/
theorem lemma_C_5 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∃ lo ∈ M.box, ∃ hi ∈ M.box,
      M.Phi lo = lo ∧ M.Phi hi = hi ∧
        ∀ rho ∈ M.box, M.Phi rho = rho → lo ≤ rho ∧ rho ≤ hi := by sorry

end MultiRegCournot.Equilibrium
