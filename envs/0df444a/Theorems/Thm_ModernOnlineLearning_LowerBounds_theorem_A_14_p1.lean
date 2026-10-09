-- Prove2me | Theorems.Thm_ModernOnlineLearning_LowerBounds_theorem_A_14_p1
-- name    : ModernOnlineLearning.LowerBounds.theorem_A_14_p1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:06.979653+00:00
-- url     : https://prove2.me/theorems/b94aa227-d5fc-4fdd-a94d-7356c9419e23
-- title:
--   Theorem A.14 (p = 1, lower bound) — Khintchine inequality
-- statement:
--   Let $N\ge1$, let $x_1,\ldots,x_N$ be real numbers, and let $\varepsilon_1,\ldots,\varepsilon_N$ be independent random signs, each equally likely to be $-1$ or $1$. The $p=1$ lower bound in Khintchine's inequality is
--
--   $$
--   \frac{1}{\sqrt2}\left(\sum_{n=1}^{N}x_n^2\right)^{1/2}
--   \le \mathbb E\left|\sum_{n=1}^{N}\varepsilon_n x_n\right|.
--   $$
--
--   This is the sharp case used to estimate a Rademacher sum in the proof of Theorem 5.1.
--
--   **Formalization Note** The signs form the uniform distribution on Boolean vectors, so the expectation is a finite average. The printed theorem also gives an upper bound and sharp constants for all $p>0$ and complex coefficients; this item formalizes only the real-coefficient $p=1$ lower bound.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem A.14, p. 296 (p = 1 lower-bound case)

import Mathlib

namespace ModernOnlineLearning.LowerBounds

/-- The lower-bound, real-coefficient `p = 1` case of Theorem A.14,
printed p. 296. Uniform `Bool` vectors are independent Rademacher signs. -/
theorem theorem_A_14_p1 {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin N, (x i) ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ *
        ∑ ω : Fin N → Bool,
          |∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * x i| := by sorry

end ModernOnlineLearning.LowerBounds
