-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_26
-- name    : FriendlyShadow.Gaussian.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:17:51.974812+00:00
-- url     : https://prove2.me/theorems/8125a087-9bfb-4ee6-be7f-ea189f611828
-- title:
--   Lemma 26, p. 23 — E[perimeter(Q ∩ W)] ≤ 2π(1 + 4rₙ)
-- statement:
--   Let $W\subseteq\mathbb R^d$ be a fixed plane and let $a_1,\dots,a_n$ be independent with probability densities whose means $\bar a_i$ satisfy $\|\bar a_i\|\le1$ and whose $n$-th deviations are at most $r$. Then the perimeter of $Q\cap W$, $Q=\operatorname{conv}(a_1,\dots,a_n)$, is a.e. measurable and
--   $$\mathbb E[\operatorname{perimeter}(Q\cap W)]\le 2\pi(1+4r) .$$
--
--   This is the numerator bound (17) in the proof of Theorem 22.
--
--   **Formalization Note** The perimeter is the sum of the edge lengths of $Q\cap W$ and its expectation is a lower Lebesgue integral in $[0,\infty]$. The hypotheses are exactly those the proof uses (centers and $n$-th deviations); the other standing assumptions of Theorem 22 are not needed.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 26, p. 23; (17), p. 32

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 26 (p. 23). Rows `a₁, …, aₙ` independent with densities `μ i`, centers (means)
of norm at most `1` and `n`-th deviations at most `r`; `W` a fixed plane. Then
`E[perimeter(Q ∩ W)] ≤ 2π(1 + 4r)`. -/
theorem lemma_26 {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : ∀ i, IsDensity (μ i)) (abar : Fin n → EuclideanSpace ℝ (Fin d))
    (hmean : ∀ i, HasMean (μ i) (abar i)) (habar : ∀ i, ‖abar i‖ ≤ 1) (r : ℝ)
    (hr : ∀ i, NthDeviationLE (μ i) (abar i) n r) :
    AEMeasurable (fun a => perimeter (polygon W a)) (rowLaw μ) ∧
    ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ) ≤ ENNReal.ofReal (2 * Real.pi * (1 + 4 * r)) := by sorry

end FriendlyShadow.Gaussian
