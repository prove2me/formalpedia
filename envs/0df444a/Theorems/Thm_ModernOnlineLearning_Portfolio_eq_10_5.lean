-- Prove2me | Theorems.Thm_ModernOnlineLearning_Portfolio_eq_10_5
-- name    : ModernOnlineLearning.Portfolio.eq_10_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:44.932148+00:00
-- url     : https://prove2.me/theorems/be90b359-de36-4025-855b-e58c6d471d50
-- title:
--   Equation (10.5), p. 176 — uniform-simplex monomial integral
-- statement:
--   Let $d\ge2$, $T\ge1$, and let $j=(j_1,\ldots,j_T)$ be a sequence of stock indices. Under the uniform prior $F_d$ on the simplex, its monomial moment is
--
--   $$\int_{\Delta^{d-1}}\prod_{t=1}^{T}x_{j_t}\,F_d(dx)=\frac{1}{\binom{T+d-1}{d-1}\,|\mathcal T_T(n(j))|},$$
--
--   where $n(j)$ is the type of $j$ and $\mathcal T_T(n(j))$ is its type class. This identity supplies the denominator in the uniform-prior regret estimate.
--
--   **Formalization Note** The uniform prior is the chart-based measure in the shared definition. The type class is finite and nonempty because it contains $j$.
-- source:
--   Orabona, arXiv:1912.13213v10, equation (10.5), proof of Theorem 10.1, p. 176

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Identity (10.5), p. 176, the uniform-simplex monomial integral. -/
theorem eq_10_5 {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (j : Fin T → Fin d) :
    (∫ p, sequenceMonomial j p ∂uniformPrior d) =
      1 / (((T + d - 1).choose (d - 1) : ℕ) : ℝ) /
        ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ) := by sorry

end ModernOnlineLearning.Portfolio
