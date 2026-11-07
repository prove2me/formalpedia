-- Prove2me | Theorems.Thm_MixScale_lemma_A_4
-- name    : MixScale.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:39.347892+00:00
-- url     : https://prove2.me/theorems/6307aadf-71f3-4060-85b9-7cbfe125f549
-- title:
--   Lemma A.4, p.15 — midpoint quadrature and oscillatory integration
-- statement:
--   Let $g:[1,2]\to\mathbb C$ be $C^1$, and $x_\ell=1+(\ell+1/2)/n$ for $0\le\ell<n$. Then
--
--   $$\Big|n^{-1}\sum_\ell g(x_\ell)-\int_1^2g(x)\,dx\Big|\le\frac{\|g'\|_\infty}{2n},$$
--
--   and for real $\omega\ne0$,
--
--   $$\Big|\int_1^2g(x)e^{i\omega x}\,dx\Big|\le\frac{|g(1)|+|g(2)|+\int_1^2|g'(x)|\,dx}{|\omega|}.$$
--
--   These two bounds control the finite-grid error and the interference between separated phases in the scalar analysis.
--
--   Differences from the source:
--   - encoding: ‖g′‖_∞ → any G bounding ‖g′‖ on [1, 2]; reason: equivalent to the supremum, which is finite for C¹ g
--   - encoding: 0 ≤ ℓ < n → 0 < n; reason: the grid is empty at n = 0 and the bound has n in a denominator
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma A.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MixScale_Scalar

namespace MixScale

/-- **Lemma A.4** (Quadrature and oscillatory integration).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma A.4, p.15 (PDF p.17).

**Formalization Note.** `g` is `C¹` on `[1, 2]`, with one-sided derivatives at the end points
(`derivWithin`). `‖g′‖_∞` is any upper bound `G`, equivalently its supremum. The grid has `n ≥ 1`
points (the grid is empty at `n = 0`). -/
theorem lemma_A_4 (g : ℝ → ℂ) (hg : ContDiffOn ℝ 1 g (Set.Icc 1 2)) :
    (∀ (n : ℕ) (G : ℝ), 0 < n → (∀ x ∈ Set.Icc (1 : ℝ) 2, ‖derivWithin g (Set.Icc 1 2) x‖ ≤ G) →
      ‖((n : ℂ)⁻¹ * ∑ l ∈ Finset.range n, g (gridPt n l)) - ∫ x in (1 : ℝ)..2, g x‖ ≤
        G / (2 * (n : ℝ))) ∧
    ∀ ω : ℝ, ω ≠ 0 →
      ‖∫ x in (1 : ℝ)..2, g x * Complex.exp ((ω * x : ℝ) * Complex.I)‖ ≤
        (‖g 1‖ + ‖g 2‖ + ∫ x in (1 : ℝ)..2, ‖derivWithin g (Set.Icc 1 2) x‖) / |ω| := by sorry

end MixScale
