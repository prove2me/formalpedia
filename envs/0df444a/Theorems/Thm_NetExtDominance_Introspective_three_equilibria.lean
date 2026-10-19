-- Prove2me | Theorems.Thm_NetExtDominance_Introspective_three_equilibria
-- name    : NetExtDominance.Introspective.three_equilibria
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:19.058189+00:00
-- url     : https://prove2.me/theorems/93de4312-10e0-4571-b926-3dce4e6c69b8
-- title:
--   §2.1, p. 8 — three equilibria between threshold prices, two at a threshold
-- statement:
--   In a market with In/Out inverse demand, fix $p_{\min}\le p\le p_{\max}$. Each of the three branches of $P$ has exactly one intersection with the price $p$, denoted $q_{\mathrm{out}}$, $q_{\mathrm{mid}}$, and $q_{\mathrm{in}}$. These intersections exhaust the equilibrium quantities:
--
--   $$D(p,q)=q\quad\Longleftrightarrow\quad q\in\{q_{\mathrm{out}},q_{\mathrm{mid}},q_{\mathrm{in}}\}\qquad(q\in[0,1]).$$
--
--   For $p_{\min}<p<p_{\max}$ they satisfy $q_{\mathrm{out}}<q_{\mathrm{mid}}<q_{\mathrm{in}}$. At $p=p_{\min}$ the out and middle intersections coincide and the in intersection is larger; at $p=p_{\max}$ the middle and in intersections coincide and the out intersection is smaller. Thus the boundary prices have two distinct equilibrium quantities.
--
--   This result supplies the branch quantities used by Proposition 1 and rules out other feasible fixed points.
--
--   **Formalization Note** Branch intersections are predicates on closed intervals, so the repeated equilibrium at a threshold belongs to two branches. Continuity of $P$ is not assumed separately; it must follow from the market assumptions.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), p. 8, §2.1, opening paragraph; http://wrap.warwick.ac.uk/178238

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting

namespace NetExtDominance.Introspective

/-- §2.1: the three branches exhaust all equilibrium quantities, with two
distinct quantities at either threshold. -/
theorem three_equilibria
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL ≤ p) (hp2 : p ≤ pmax M.P QH) :
    (∃! q, IsQout M.P QL p q) ∧
      (∃! q, IsQmid M.P QL QH p q) ∧
      (∃! q, IsQin M.P QH p q) ∧
      ∀ qo qm qi,
        IsQout M.P QL p qo →
        IsQmid M.P QL QH p qm →
        IsQin M.P QH p qi →
        (∀ q, IsEquilibriumQty M p q ↔ (q = qo ∨ q = qm ∨ q = qi)) ∧
        (pmin M.P QL < p → p < pmax M.P QH → qo < qm ∧ qm < qi) ∧
        (p = pmin M.P QL → qo = qm ∧ qm < qi) ∧
        (p = pmax M.P QH → qo < qm ∧ qm = qi) := by sorry

end NetExtDominance.Introspective
