-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_6_part_3
-- name    : JSQHalfinWhitt.Tightness.lemma_6_part_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:56.591922+00:00
-- url     : https://prove2.me/theorems/4bcc3bc1-76d9-41ca-86cd-1f540d803945
-- title:
--   Lemma 6, part 3 — for $\beta < \kappa_1 < \kappa_2$, $x \ge \Gamma^{(\kappa_2)}$ implies $x > \Gamma^{(\kappa_1)}$ (4.13)
-- statement:
--   Let $n \ge 1$ and $0 < \beta < \sqrt n$, and let $\Gamma^{(\kappa)} = \{x \in \Omega \mid x_2 = \nu^*(x_1)\}$ be the curve of Lemma 5, with $\nu^*$ depending on $\kappa$. For any $\kappa_1, \kappa_2$ with $\beta < \kappa_1 < \kappa_2$ and every $x \in \Omega$,
--   $$x \ge \Gamma^{(\kappa_2)} \implies x > \Gamma^{(\kappa_1)}, \tag{4.13}$$
--   i.e. the curve $\Gamma^{(\kappa_2)}$ lies strictly above $\Gamma^{(\kappa_1)}$.
--
--   **Formalization Note** With $\nu^*_{\kappa}$ the function of Lemma 5 for the parameter $\kappa$, the statement is: $x_1 \le 0$, $x_2 \ge 0$ and $x_2 \ge \nu^*_{\kappa_2}(x_1)$ imply $x_2 > \nu^*_{\kappa_1}(x_1)$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 13, Lemma 6, part 3, (4.13)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

namespace JSQHalfinWhitt.Tightness

/-- Lemma 6, part 3 (Braverman, p. 13), (4.13): for `β < κ_1 < κ_2` and `x ∈ Ω`,
`x ≥ Γ^{(κ_2)}` implies `x > Γ^{(κ_1)}`: the curve `Γ^{(κ_2)}` lies strictly above `Γ^{(κ_1)}`. -/
theorem lemma_6_part_3 (n : ℕ) (β κ₁ κ₂ : ℝ) (hn : 1 ≤ n) (hβ : 0 < β)
    (hβn : β < Real.sqrt n) (hκ₁ : β < κ₁) (hκ₁₂ : κ₁ < κ₂) (x : ℝ × ℝ) (hx1 : x.1 ≤ 0)
    (hx2 : 0 ≤ x.2) (hxΓ : nuStar β κ₂ n x.1 ≤ x.2) :
    nuStar β κ₁ n x.1 < x.2 := by sorry

end JSQHalfinWhitt.Tightness
