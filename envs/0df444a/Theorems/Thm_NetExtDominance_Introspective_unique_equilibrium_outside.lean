-- Prove2me | Theorems.Thm_NetExtDominance_Introspective_unique_equilibrium_outside
-- name    : NetExtDominance.Introspective.unique_equilibrium_outside
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:22.047483+00:00
-- url     : https://prove2.me/theorems/17cb64f1-a59c-4009-ae6d-ed5a306885ae
-- title:
--   Proof of Proposition 1, p. 10 — unique equilibrium outside the threshold prices
-- statement:
--   In a market with In/Out inverse demand, suppose the relative price lies outside the interval of multiple equilibria, so $p>p_{\max}$ or $p<p_{\min}$. Then there is exactly one feasible equilibrium quantity:
--
--   $$\exists!q\in[0,1],\quad D(p,q)=q.$$
--
--   This supplies the unique equilibrium named in the second part of Proposition 1.
--
--   **Formalization Note** An equilibrium is a fixed point of aggregate demand, including at $q=0$ or $q=1$. At prices beyond $P(0)$ or $P(1)$ there need not be a solution to $P(q)=p$; the proof paragraph's claim about an inverse-demand intersection is read as the stated fixed-point claim.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), p. 10, proof of Proposition 1, second paragraph; http://wrap.warwick.ac.uk/178238

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting

namespace NetExtDominance.Introspective

/-- Proof of Proposition 1, second paragraph: outside the threshold prices
there is a unique feasible fixed point of aggregate demand. -/
theorem unique_equilibrium_outside
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp : pmax M.P QH < p ∨ p < pmin M.P QL) :
    ∃! q, IsEquilibriumQty M p q := by sorry

end NetExtDominance.Introspective
