-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_6_part_1
-- name    : JSQHalfinWhitt.Tightness.lemma_6_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:03.498426+00:00
-- url     : https://prove2.me/theorems/5eae18b5-3251-444d-a799-13b4b8333d10
-- title:
--   Lemma 6, part 1 — above $\Gamma^{(\kappa)}$, $\tau(x) < \infty$ and $x_2e^{-\tau(x)} > \kappa/\sqrt n$; on $\Gamma^{(\kappa)}$, equality
-- statement:
--   Let $n \ge 1$ and $0 < \beta < \sqrt n$. Fix $\kappa \ge \beta$ and $x \in (-\infty, 0] \times [\kappa/\sqrt n, \infty)$, and let $\tau$ be the hitting time of Lemma 6 and $\Gamma^{(\kappa)} = \{x \in \Omega \mid x_2 = \nu^*(x_1)\}$ the curve of Lemma 5.
--
--   1. If $x > \Gamma^{(\kappa)}$, i.e. $x_2 > \nu^*(x_1)$, then $\tau(x) < \infty$ and
--   $$x_2 e^{-\tau(x)} > \kappa/\sqrt n. \tag{4.11}$$
--   2. If $x \in \Gamma^{(\kappa)}$, then $\tau(x) < \infty$ and $x_2 e^{-\tau(x)} = \kappa/\sqrt n$.
--
--   A fluid path started above $\Gamma^{(\kappa)}$ meets the vertical axis above the level $\kappa/\sqrt n$, and one started on the curve meets it exactly at that level.
--
--   **Formalization Note** "$\tau(x) < \infty$ and $P(\tau(x))$" is written as "there is a real $t$ with $\tau(x) = t$ and $P(t)$". Only part 1 of Lemma 6 is stated here; (4.10), part 2 and part 3 are separate items.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 13, Lemma 6, part 1, (4.11)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

namespace JSQHalfinWhitt.Tightness

/-- Lemma 6, part 1 (Braverman, p. 13): fix `κ ≥ β` and `x ∈ (−∞, 0] × [κ/√n, ∞)`. If
`x > Γ^{(κ)}` (i.e. `x_2 > ν^*(x_1)`), then `τ(x) < ∞` and `x_2 e^{−τ(x)} > κ/√n` (4.11); if
`x ∈ Γ^{(κ)}`, then `τ(x) < ∞` and `x_2 e^{−τ(x)} = κ/√n`. -/
theorem lemma_6_part_1 (n : ℕ) (β κ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (hκ : β ≤ κ) (x : ℝ × ℝ) (hx1 : x.1 ≤ 0) (hx2 : κ / Real.sqrt n ≤ x.2) :
    (nuStar β κ n x.1 < x.2 →
        ∃ t : ℝ, tau β n x = t ∧ κ / Real.sqrt n < x.2 * Real.exp (-t)) ∧
      (x ∈ gammaCurve β κ n →
        ∃ t : ℝ, tau β n x = t ∧ x.2 * Real.exp (-t) = κ / Real.sqrt n) := by sorry

end JSQHalfinWhitt.Tightness
