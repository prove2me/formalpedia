-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_eq_33
-- name    : MultiPriceOnline.Ratios.eq_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:53.63615+00:00
-- url     : https://prove2.me/theorems/cff9e580-771a-4d55-85ef-063be763fe12
-- title:
--   (33), App. A, p. 39 — α⁽¹⁾ is the unique solution of α⁽¹⁾ + Σⱼ −ln(1 − (1 − e^{−α⁽¹⁾})(1 − r⁽ʲ⁻¹⁾/r⁽ʲ⁾)) = 1
-- statement:
--   Let $m \ge 2$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set, and let $\alpha^{(1)}, \dots, \alpha^{(m)}$ be the booking limits (positive, summing to $1$, satisfying (7)). Then $\alpha^{(1)}$ solves
--   $$x + \sum_{j=2}^{m} \Bigl[-\ln\Bigl(1 - \bigl(1 - e^{-x}\bigr)\Bigl(1 - \frac{r^{(j-1)}}{r^{(j)}}\Bigr)\Bigr)\Bigr] = 1, \qquad (33)$$
--   and every real $x$ solving (33) equals $\alpha^{(1)}$.
--
--   Equation (33) eliminates $\alpha^{(2)}, \dots, \alpha^{(m)}$ from Proposition 1, so that $\alpha^{(1)}$, hence $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$, is characterized by a single scalar equation. It is compared with (34) to prove (13).
--
--   **Formalization Note** The paper says "the unique solution"; uniqueness is stated over all real $x$ (not only over $(0,1)$, where the paper's monotonicity argument is carried out).
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 39, App. A, proof of Proposition 2, (33)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

open Finset

theorem eq_33 (m : ℕ) (hm : 2 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    (α 1 + ∑ j ∈ Icc 2 m,
        -Real.log (1 - (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j)) = 1) ∧
    ∀ x : ℝ,
      x + ∑ j ∈ Icc 2 m,
          -Real.log (1 - (1 - Real.exp (-x)) * (1 - r (j - 1) / r j)) = 1 →
        x = α 1 := by sorry

end MultiPriceOnline.Ratios
