-- Prove2me | Theorems.Thm_KLTNuclear_Lasso_gaussian_tail
-- name    : KLTNuclear.Lasso.gaussian_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:36.577316+00:00
-- url     : https://prove2.me/theorems/a327c7d2-399c-4a00-bf31-8c815eee9f5b
-- title:
--   Proof of Theorem 14, p. 25 — the standard Gaussian tail bound P(|N| > z) ≤ √(2/π) e^{−z²/2}/z
-- statement:
--   Let $N$ be a standard normal random variable, $N\sim\mathcal N(0,1)$. For every $z>0$,
--   $$
--   P(|N| > z) \le \sqrt{\frac2\pi}\,\frac{e^{-z^2/2}}{z}.
--   $$
--
--   This is the "standard bound on the tail of the Gaussian distribution" that the proof of Theorem 14 combines with a union bound over the $p$ coordinates of $\mathbf M$.
--
--   **Formalization Note** The paper invokes this bound without stating it; this is its usual form (Mills' ratio), and it is what reproduces the paper's probability $1/(p^{b^2-1}\sqrt{\pi\log p})$. The probability is the measure `gaussianReal 0 1` of the set $\{y : z < |y|\}$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 25, proof of Theorem 14 ('a standard bound on the tail of the Gaussian distribution')

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace KLTNuclear.Lasso

/-- The standard bound on the tail of the Gaussian distribution invoked in the proof of
Theorem 14, arXiv:1011.6256v4, p. 25: for a standard normal variable `N ~ 𝒩(0, 1)` and every
`z > 0`, `P(|N| > z) ≤ √(2/π) e^{−z²/2} / z`. -/
theorem gaussian_tail {z : ℝ} (hz : 0 < z) :
    gaussianReal 0 1 {y : ℝ | z < |y|} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-(z ^ 2) / 2) / z) := by sorry

end KLTNuclear.Lasso
