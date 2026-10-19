-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_C_3
-- name    : MultiRegCournot.Equilibrium.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:47.227972+00:00
-- url     : https://prove2.me/theorems/7423dd2b-3302-4d8b-8a65-0367d6780aa9
-- title:
--   Lemma C.3, p. 33 — single crossing of regional participation
-- statement:
--   Fix a firm i, a region r, and all other firms' marginal profits. There is a threshold c such that firm i sells a positive amount in region r at its own marginal profit x exactly when x<c.
--
--   $$\hat q_r^i(x,\rho^{-i})>0\quad\Longleftrightarrow\quad x<c.$$
--
--   The threshold describes how the active set changes as one firm's marginal profit rises.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs. The equivalence is stated for x∈[0,w̄] and the other coordinates drawn from the box.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 33, Lemma C.3

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma C.3, p. 33: the active-firm threshold in a region. -/
theorem lemma_C_3 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∀ rho ∈ M.box, ∀ i r, ∃ c : ℝ,
      ∀ x ∈ Set.Icc (0 : ℝ) M.wbar,
        (0 < M.Qhat (Function.update rho i x) i r ↔ x < c) := by sorry

end MultiRegCournot.Equilibrium
