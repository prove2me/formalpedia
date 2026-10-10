-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_eq_29
-- name    : MultiPriceOnline.Hardness.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:02.642104+00:00
-- url     : https://prove2.me/theorems/485f05b9-b1de-4241-b430-77cc50750e9a
-- title:
--   (29), p. 25 — nk Σ r⁽ℓ⁾Bℓ(1 − e^{−α⁽ℓ⁾}) = (1 − e^{−α⁽¹⁾}) Σ (r⁽ℓ⁾ − r⁽ℓ⁻¹⁾)Bℓnk
-- statement:
--   Let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set with booking limits $\alpha^{(1)}, \dots, \alpha^{(m)}$ (Proposition 1), and recall $r^{(0)} = 0$. For all real numbers $B_1, \dots, B_m$ and all $n, k \in \mathbb N$,
--
--   $$nk \sum_{\ell=1}^m r^{(\ell)} B_\ell \big(1 - e^{-\alpha^{(\ell)}}\big) = \big(1 - e^{-\alpha^{(1)}}\big) \sum_{\ell=1}^m \big(r^{(\ell)} - r^{(\ell-1)}\big) B_\ell n k.$$
--
--   The left side is the value (28) at $j = 1$, $\tau = 1$. The right side is $F(\mathcal P)$ times the expression (25) for OPT. This identity is the step of the proof of Theorem 3 that produces the factor $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 25, eq. (29) in the proof of Theorem 3

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet

namespace MultiPriceOnline.Hardness
open Finset
theorem eq_29 {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α)
    (B : ℕ → ℝ) (n k : ℕ) :
    (n : ℝ) * k * ∑ l ∈ Icc 1 m, r l * B l * (1 - Real.exp (-α l)) =
      (1 - Real.exp (-α 1)) * ∑ l ∈ Icc 1 m, (price r l - price r (l - 1)) * B l * n * k := by sorry
end MultiPriceOnline.Hardness
