-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_eq_34
-- name    : MultiPriceOnline.Ratios.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:00.470305+00:00
-- url     : https://prove2.me/theorems/a7e2a004-266d-466e-b8d2-2a08008ae461
-- title:
--   (34), App. A, p. 39 — the root of 1 − e^{−α} = (1 − α)/ln(r⁽ᵐ⁾/r⁽¹⁾) is the unique solution of α + Σⱼ (1 − e^{−α}) ln(r⁽ʲ⁾/r⁽ʲ⁻¹⁾) = 1
-- statement:
--   Let $m \ge 2$ and let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set. Then:
--
--   1. a real number $a$ solves
--   $$1 - e^{-a} = \frac{1 - a}{\ln(r^{(m)}/r^{(1)})} \qquad (13)$$
--   if and only if it solves
--   $$a + \sum_{j=2}^{m} \bigl(1 - e^{-a}\bigr)\ln\frac{r^{(j)}}{r^{(j-1)}} = 1; \qquad (34)$$
--   2. equation (34) has exactly one real solution;
--   3. every solution of (34) lies in the open interval $(0, 1)$.
--
--   The solution $\alpha$ defines $1 - e^{-\alpha}$, the paper's competitive ratio when every item may be priced anywhere in the continuum $[r^{(1)}, r^{(m)}]$; (34) puts it in the same form as (33), which is how (13) is proved.
--
--   **Formalization Note** Items 2 and 3 make precise the paper's phrase "$\alpha$ is the unique solution". The logarithm $\ln(r^{(m)}/r^{(1)})$ is positive for $m \ge 2$, so the division in (13) is by a nonzero number.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 39, App. A, proof of Proposition 2, (34); p. 17, (13)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

open Finset

theorem eq_34 (m : ℕ) (hm : 2 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    (∀ a : ℝ, 1 - Real.exp (-a) = (1 - a) / Real.log (r m / r 1) ↔
      a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1) ∧
    (∃! a : ℝ, a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1) ∧
    ∀ a : ℝ, a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1 →
      0 < a ∧ a < 1 := by sorry

end MultiPriceOnline.Ratios
