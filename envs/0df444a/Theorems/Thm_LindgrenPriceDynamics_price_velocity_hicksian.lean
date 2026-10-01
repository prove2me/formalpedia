-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_price_velocity_hicksian
-- name    : LindgrenPriceDynamics.price_velocity_hicksian
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T18:31:04.454991+00:00
-- url     : https://prove2.me/theorems/db149e85-2444-4cca-a275-69ba0f596ed7
-- title:
--   Price velocity driven by Hicksian demand: $m\partial_tv_i+\frac m2\nabla_i(v^kv_k)=\lambda^jh^j_i$
-- statement:
--   Under the hypotheses of eq. (12) — $m>0$, $J$ of class $C^2$ solving the HJB equation (10), $v=-\frac1m\nabla J$ — assume in addition that each expenditure function $e_j$ is differentiable and that the Hicksian demands $h^j(p)\in\mathbb R^l$ are given by Shephard's lemma (13), $h^j_i=\partial e_j/\partial p_i$. Then for all $t,p,i$,
--
--   $$m\,\frac{\partial v_i}{\partial t}(t,p)+\tfrac12 m\,\frac{\partial}{\partial p_i}\langle v(t,\cdot),v(t,\cdot)\rangle(p)=\sum_{j=1}^n\lambda_j\,h^j_i(p).$$
--
--   The weighted aggregate Hicksian demand is the force that drives price adjustment.
--
--   **Formalization Note** Shephard's lemma is cited, not proved, in the paper; here it enters as the hypothesis $h^j_i=\partial e_j/\partial p_i$.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, p. 31, eqs. (13)–(14)

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Eq. (14): under the hypotheses of eq. (12), with differentiable expenditure functions
and Hicksian demands given by Shephard's lemma (13) `h^j_i = ∇_i e_j`, the optimal
price velocity satisfies `m ∂v_i/∂t + ½ m ∇_i (v^k v_k) = λ^j h^j_i`. -/
theorem price_velocity_hicksian {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (he : ∀ j, Differentiable ℝ (e j))
    (h : Fin n → (Fin l → ℝ) → Fin l → ℝ)
    (hShephard : ∀ j p i, h j p i = pricePartial (e j) p i)
    (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 2 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ t p, timePartial J t p =
      dot (priceGrad (J t) p) (priceGrad (J t) p) / (2 * m) - aggregateExpenditure lam e p) :
    ∀ t p i,
      m * timePartial (fun τ q => optimalVelocity m J τ q i) t p
        + (1 / 2) * m * pricePartial
            (fun q => dot (optimalVelocity m J t q) (optimalVelocity m J t q)) p i
        = ∑ j, lam j * h j p i := by
  sorry

end LindgrenPriceDynamics
