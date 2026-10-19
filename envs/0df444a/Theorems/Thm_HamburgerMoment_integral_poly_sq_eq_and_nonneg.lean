-- Prove2me | Theorems.Thm_HamburgerMoment_integral_poly_sq_eq_and_nonneg
-- name    : HamburgerMoment.integral_poly_sq_eq_and_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:05:49.525607+00:00
-- url     : https://prove2.me/theorems/f86604b0-54ea-4927-92ac-4c7e44af07ea
-- title:
--   $\int p(x)^2\,d\mu=\sum_{j,k}a_ja_km_{j+k}\ge0$ for real polynomials $p$
-- statement:
--   Let $\mu$ be a solution of the Hamburger moment problem for the real sequence $m$. Then for every $n\ge0$ and every real polynomial
--   $$p(x)=\sum_{j=0}^{n}a_jx^j\qquad(a_0,\dots,a_n\in\mathbb R)$$
--   one has
--   $$\int p(x)^2\,d\mu=\int\Big(\sum_{j,k=0}^{n}a_ja_kx^{j+k}\Big)d\mu=\sum_{j,k=0}^{n}a_ja_km_{j+k}\ \ge\ 0.$$
--
--   This is the statement that each real Hankel matrix $\Delta_n$ of a moment sequence is positive semidefinite.
--
--   **Formalization Note** The coefficients are given as a function `a : ℕ → ℝ`, of which only $a_0,\dots,a_n$ are used.
-- source:
--   Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Polynomials", displayed identity

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem integral_poly_sq_eq_and_nonneg (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsMomentMeasure m μ) (n : ℕ) (a : ℕ → ℝ) :
    ∫ x, (∑ j ∈ Finset.range (n + 1), a j * x ^ j) ^ 2 ∂μ =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), a j * a k * m (j + k) ∧
      0 ≤ ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), a j * a k * m (j + k) := by sorry

end HamburgerMoment
