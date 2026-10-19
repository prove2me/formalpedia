-- Prove2me | Theorems.Thm_NetExtDominance_Introspective_footnote_12_sign
-- name    : NetExtDominance.Introspective.footnote_12_sign
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:14.597726+00:00
-- url     : https://prove2.me/theorems/9e01f7b0-66b2-44ec-bd4f-efc3e3d8c3be
-- title:
--   Footnote 12, p. 10 — sign of aggregate demand relative to the 45° line
-- statement:
--   Let $D$ and $P$ be a market with In/Out inverse demand, let $p_{\min}\le p\le p_{\max}$, and choose branch intersections $q_{\mathrm{out}}$, $q_{\mathrm{mid}}$, $q_{\mathrm{in}}$ at price $p$. All three are fixed points of $D(p,\cdot)$. For every $x\in[0,1]$,
--
--   $$
--   \begin{aligned}
--   q_{\mathrm{mid}}<x<q_{\mathrm{in}}&\implies D(p,x)>x,\\
--   x>q_{\mathrm{in}}&\implies D(p,x)<x,\\
--   q_{\mathrm{out}}<x<q_{\mathrm{mid}}&\implies D(p,x)<x,\\
--   x<q_{\mathrm{out}}&\implies D(p,x)>x.
--   \end{aligned}
--   $$
--
--   This records the crossing pattern in Figure 1(b) that determines the direction of the level-$k$ dynamics.
--
--   **Formalization Note** At a threshold price, two branch intersections may coincide; the corresponding open interval is empty. The market's strict price signs apply only away from the saturation endpoints.
-- source:
--   Akerlof, Holden & Rayo, Network Externalities and Market Dominance, author's accepted manuscript (WRAP 178238, dated September 16, 2022), p. 10, footnote 12; http://wrap.warwick.ac.uk/178238

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting

namespace NetExtDominance.Introspective

/-- Footnote 12: the demand map lies above or below the 45-degree line on the
successive intervals cut out by the three inverse-demand intersections. -/
theorem footnote_12_sign
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL ≤ p) (hp2 : p ≤ pmax M.P QH)
    (qo qm qi : ℝ) (ho : IsQout M.P QL p qo)
    (hm : IsQmid M.P QL QH p qm) (hi : IsQin M.P QH p qi) :
    M.D p qo = qo ∧ M.D p qm = qm ∧ M.D p qi = qi ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (qm < x → x < qi → x < M.D p x) ∧
        (qi < x → M.D p x < x) ∧
        (qo < x → x < qm → M.D p x < x) ∧
        (x < qo → x < M.D p x) := by sorry

end NetExtDominance.Introspective
