-- Prove2me | Theorems.Thm_NetExtDominance_Introspective_converge_by_side
-- name    : NetExtDominance.Introspective.converge_by_side
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:30.167343+00:00
-- url     : https://prove2.me/theorems/3a945996-f9d6-470f-946c-9d6f07ee664b
-- title:
--   Proof of Proposition 1, p. 10 — convergence from either side of the middle equilibrium
-- statement:
--   Let the market have In/Out inverse demand and $p_{\min}\le p\le p_{\max}$. Choose the out, middle, and in branch equilibria $q_{\mathrm{out}}$, $q_{\mathrm{mid}}$, and $q_{\mathrm{in}}$. For any impulse $I_0\in[0,1]$, the sequence $I_k=D(p,\cdot)^{\circ k}(I_0)$ satisfies
--
--   $$
--   \begin{cases}
--   I_k\to q_{\mathrm{in}},& I_0>q_{\mathrm{mid}},\\
--   I_k=I_0\text{ for every }k,& I_0=q_{\mathrm{mid}},\\
--   I_k\to q_{\mathrm{out}},& I_0<q_{\mathrm{mid}}.
--   \end{cases}
--   $$
--
--   This is the convergence claim in the first paragraph of the proof of Proposition 1.
--
--   **Formalization Note** At a threshold price, adjacent branch equilibria may coincide; the three implications still have their stated meanings.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), p. 10, proof of Proposition 1, first paragraph; http://wrap.warwick.ac.uk/178238

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting

namespace NetExtDominance.Introspective

/-- Proof of Proposition 1, first paragraph: the impulse's side of the middle
equilibrium determines the limit, and the middle point remains fixed. -/
theorem converge_by_side
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL ≤ p) (hp2 : p ≤ pmax M.P QH)
    (qo qm qi : ℝ) (ho : IsQout M.P QL p qo)
    (hm : IsQmid M.P QL QH p qm) (hi : IsQin M.P QH p qi)
    (I0 : ℝ) (hI0 : I0 ∈ Set.Icc (0 : ℝ) 1) :
    (qm < I0 → IsIntrospectiveEq M p I0 qi) ∧
      (I0 < qm → IsIntrospectiveEq M p I0 qo) ∧
      (I0 = qm → ∀ k, levelK M p I0 k = I0) := by sorry

end NetExtDominance.Introspective
