-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_price_normalization_orthogonal
-- name    : LindgrenPriceDynamics.price_normalization_orthogonal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T17:56:00.528344+00:00
-- url     : https://prove2.me/theorems/1fd9e21e-18d2-4c93-a0c2-3592c6c586f8
-- title:
--   Normalized prices move orthogonally: $p^i\,dp_i/ds=0$
-- statement:
--   Let $p:\mathbb R\to\mathbb R^l$ be a price path normalized so that $\langle p(s),p(s)\rangle=\sum_i p_i(s)^2=1$ for every time $s$. If $p$ is differentiable at $s$, then
--
--   $$\langle p(s),\dot p(s)\rangle=\sum_{i=1}^l p_i(s)\,\frac{dp_i}{ds}(s)=0 .$$
--
--   This is the normalization identity used in the paper to fix the scale of prices, which is possible because excess demand is homogeneous of degree zero.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, p. 28, eq. (4)

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Eq. (4): normalized prices `p^i p_i = 1` move orthogonally, `p_i dp^i/ds = 0`. -/
theorem price_normalization_orthogonal {l : ℕ} (p : ℝ → Fin l → ℝ)
    (hnorm : ∀ s, dot (p s) (p s) = 1) (s : ℝ) (hp : DifferentiableAt ℝ p s) :
    dot (p s) (deriv p s) = 0 := by sorry

end LindgrenPriceDynamics
