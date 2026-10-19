-- Prove2me | Theorems.Thm_NetExtDominance_Introspective_proposition_1
-- name    : NetExtDominance.Introspective.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:14.42289+00:00
-- url     : https://prove2.me/theorems/2cc51565-ace6-41fe-97be-a485b9a5ee69
-- title:
--   Proposition 1, p. 10 — the impulse selects the introspective equilibrium under In/Out demand
-- statement:
--   Suppose a market's inverse demand curve is In/Out, with thresholds $p_{\min}=P(Q_L)$ and $p_{\max}=P(Q_H)$. Start the level-$k$ recursion $I_k=D(p,\cdot)^{\circ k}(I_0)$ from an impulse $I_0\in[0,1]$.
--
--   For $p_{\min}\le p\le p_{\max}$, the out, middle, and in branch equilibria all exist, and the introspective equilibrium selected by the impulse is
--
--   $$
--   Q_1^*(p)=
--   \begin{cases}
--   Q^{\mathrm{in}}(p),& I_0>Q^{\mathrm{mid}}(p),\\
--   Q^{\mathrm{mid}}(p),& I_0=Q^{\mathrm{mid}}(p),\\
--   Q^{\mathrm{out}}(p),& I_0<Q^{\mathrm{mid}}(p).
--   \end{cases}
--   $$
--
--   For $p>p_{\max}$ or $p<p_{\min}$ there is exactly one feasible equilibrium quantity $q$ satisfying $D(p,q)=q$, and the level-$k$ sequence converges to $q$ for every allowed impulse.
--
--   This is the paper's selection rule for continuation-game equilibrium quantities.
--
--   **Formalization Note** At a threshold price two branch quantities coincide. The existence clause prevents empty branch predicates from making the selection rule vacuous. Outside the threshold interval the equilibrium is defined by $D(p,q)=q$, so the statement covers saturated equilibria where $P(q)=p$ has no solution. The market's strict demand signs at inverse-demand points disclose the reading of “decreasing” used in footnote 12; weak monotonicity in quantity replaces the paper's stronger phrase, which fails in its saturated consumer model.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), p. 10, Proposition 1; http://wrap.warwick.ac.uk/178238

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting

namespace NetExtDominance.Introspective

/-- Proposition 1: the impulse selects one of the three introspective
equilibria between the threshold prices, and the unique equilibrium outside. -/
theorem proposition_1
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (I0 : ℝ) (hI0 : I0 ∈ Set.Icc (0 : ℝ) 1) (p : ℝ) :
    ((pmin M.P QL ≤ p → p ≤ pmax M.P QH →
      (∃ qo qm qi,
        IsQout M.P QL p qo ∧
        IsQmid M.P QL QH p qm ∧
        IsQin M.P QH p qi) ∧
      ∀ qo qm qi,
        IsQout M.P QL p qo →
        IsQmid M.P QL QH p qm →
        IsQin M.P QH p qi →
        (qm < I0 → IsIntrospectiveEq M p I0 qi) ∧
        (I0 = qm → IsIntrospectiveEq M p I0 qm) ∧
        (I0 < qm → IsIntrospectiveEq M p I0 qo)) ∧
      ((pmax M.P QH < p ∨ p < pmin M.P QL) →
        ∃ q, IsEquilibriumQty M p q ∧
          (∀ q', IsEquilibriumQty M p q' → q' = q) ∧
          IsIntrospectiveEq M p I0 q)) := by sorry

end NetExtDominance.Introspective
