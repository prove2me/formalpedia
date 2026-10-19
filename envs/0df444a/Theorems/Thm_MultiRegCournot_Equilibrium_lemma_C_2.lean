-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_C_2
-- name    : MultiRegCournot.Equilibrium.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:48.143167+00:00
-- url     : https://prove2.me/theorems/d6d2d2e9-6d95-4628-b3b3-2c60f4af022c
-- title:
--   Lemma C.2, p. 33 — continuity of the allocation and totals
-- statement:
--   As the marginal-profit vector ρ varies over its box, every allocation coordinate Q̂ⁱᵣ(ρ) is continuous. Consequently, each firm's total output and each region's total sales are continuous functions of ρ.
--
--   $$\rho\mapsto\hat q_r^i(\rho),\quad\rho\mapsto\hat q_{tot}^i(\rho),\quad\rho\mapsto\hat q_r^{tot}(\rho)\quad\text{are continuous.}$$
--
--   The continuity is used to establish the active-firm thresholds and the inverse in Φ.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs. Continuity is asserted on the domain [0,w̄]ᴺ of Q̂.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 33, Lemma C.2

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma C.2, p. 33. -/
theorem lemma_C_2 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    (∀ i r, ContinuousOn (fun rho => M.Qhat rho i r) M.box) ∧
      (∀ i, ContinuousOn (fun rho => qTotFirm (M.Qhat rho) i) M.box) ∧
      ∀ r, ContinuousOn (fun rho => qTotRegion (M.Qhat rho) r) M.box := by sorry

end MultiRegCournot.Equilibrium
