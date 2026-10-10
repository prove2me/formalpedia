-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_proposition_2
-- name    : MultiPriceOnline.Ratios.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:32.927437+00:00
-- url     : https://prove2.me/theorems/9e1b5b87-5ffa-43ea-8fd3-b28fd78045f6
-- title:
--   Proposition 2, p. 17 — (1 − 1/e)σ⁽¹⁾ < 1 − e^{−σ⁽¹⁾} < 1 − e^{−α⁽¹⁾}, 1/(1 + ln(r⁽ᵐ⁾/r⁽¹⁾)) < σ⁽¹⁾, and 1 − e^{−α} < 1 − e^{−α⁽¹⁾}
-- statement:
--   Let $m \ge 2$ and let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set. Let $\alpha^{(1)}, \dots, \alpha^{(m)}$ be its booking limits (positive, summing to $1$, satisfying (7)) and $\sigma^{(1)}, \dots, \sigma^{(m)}$ its Ball–Queyranne limits (positive, summing to $1$, satisfying (8)). Then
--   $$\Bigl(1 - \frac1e\Bigr)\sigma^{(1)} < 1 - e^{-\sigma^{(1)}} < 1 - e^{-\alpha^{(1)}}, \qquad (11)$$
--   $$\frac{1}{1 + \ln\bigl(r^{(m)}/r^{(1)}\bigr)} < \sigma^{(1)}, \qquad (12)$$
--   and, for the real number $\alpha$ solving $1 - e^{-\alpha} = (1 - \alpha)/\ln(r^{(m)}/r^{(1)})$,
--   $$1 - e^{-\alpha} < 1 - e^{-\alpha^{(1)}}. \qquad (13)$$
--
--   The proposition places the paper's tight ratio $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$ among known ratios: $\sigma^{(1)}$ is the tight ratio for a single item with price set $\mathcal P$ and $1 - 1/e$ the tight ratio for many single-price items, and (11) shows that $F(\mathcal P)$ strictly exceeds their naive combination $(1 - 1/e)\sigma^{(1)}$. Inequalities (12) and (13) say that restricting the price continuum $[r^{(1)}, r^{(m)}]$ to the discrete set $\mathcal P$ strictly raises the tight ratio, for one item and for many items respectively.
--
--   **Formalization Note** The booking limits enter as arbitrary families satisfying (7) resp. (8) with positivity and sum $1$; by Proposition 1 these are the paper's $\alpha^{(j)}$, $\sigma^{(j)}$. The constant $1 - 1/e$ is written $1 - e^{-1}$. Clause (13) is stated for every real root $a$ of $1 - e^{-a} = (1-a)/\ln(r^{(m)}/r^{(1)})$; since this equation has exactly one real root for $m \ge 2$ (milestone (34)), this is the paper's statement about "the unique solution", and it is not vacuous. The hypothesis $m \ge 2$ is the paper's: for $m = 1$ one has $\sigma^{(1)} = \alpha^{(1)} = 1$ and $\ln(r^{(m)}/r^{(1)}) = 0$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 17, Proposition 2, (11)–(13)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

theorem proposition_2 (m : ℕ) (hm : 2 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (σ : ℕ → ℝ) (hσ : MultiPriceOnline.Balance.IsBQLimits m r σ) :
    ((1 - Real.exp (-1)) * σ 1 < 1 - Real.exp (-σ 1) ∧
      1 - Real.exp (-σ 1) < 1 - Real.exp (-α 1)) ∧
    1 / (1 + Real.log (r m / r 1)) < σ 1 ∧
    ∀ a : ℝ, 1 - Real.exp (-a) = (1 - a) / Real.log (r m / r 1) →
      1 - Real.exp (-a) < 1 - Real.exp (-α 1) := by sorry

end MultiPriceOnline.Ratios
