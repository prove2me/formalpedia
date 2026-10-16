-- Prove2me | Theorems.Thm_NetExtDominance_Introspective_converge_outside
-- name    : NetExtDominance.Introspective.converge_outside
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:16.5211+00:00
-- url     : https://prove2.me/theorems/72218206-ea76-40d3-80e6-33f06e316bc4
-- title:
--   Proof of Proposition 1, p. 10 — convergence to the unique equilibrium from every impulse
-- statement:
--   In a market with In/Out inverse demand, suppose $p>p_{\max}$ or $p<p_{\min}$, and let $q\in[0,1]$ be an equilibrium quantity, $D(p,q)=q$. Every impulse $I_0\in[0,1]$ produces level-$k$ consumption converging to $q$:
--
--   $$D(p,\cdot)^{\circ k}(I_0)\longrightarrow q\qquad(k\to\infty).$$
--
--   With uniqueness of the equilibrium quantity, this establishes impulse independence outside the threshold interval.
--
--   **Formalization Note** The equilibrium hypothesis refers to aggregate demand, including saturated quantities at $0$ and $1$.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), p. 10, proof of Proposition 1, second paragraph; http://wrap.warwick.ac.uk/178238

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting

namespace NetExtDominance.Introspective

/-- Proof of Proposition 1, second paragraph: every admissible impulse
converges to the unique equilibrium outside the threshold prices. -/
theorem converge_outside
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp : pmax M.P QH < p ∨ p < pmin M.P QL)
    (q : ℝ) (hq : IsEquilibriumQty M p q)
    (I0 : ℝ) (hI0 : I0 ∈ Set.Icc (0 : ℝ) 1) :
    IsIntrospectiveEq M p I0 q := by sorry

end NetExtDominance.Introspective
