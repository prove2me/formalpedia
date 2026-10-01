-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_price_velocity_evolution
-- name    : LindgrenPriceDynamics.price_velocity_evolution
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T18:27:50.406245+00:00
-- url     : https://prove2.me/theorems/0384a889-85cf-4b71-8088-4a8bd9eec755
-- title:
--   Evolution equation for the price velocity: $m\partial_tv_i+\frac m2\nabla_i(v^kv_k)=\nabla_i(\lambda^je_j)$
-- statement:
--   Let $m>0$, weights $\lambda_j$, expenditure functions $e_j$, and let $J(t,p)$ be twice continuously differentiable in $(t,p)\in\mathbb R\times\mathbb R^l$ and solve the HJB equation (10):
--   $$\frac{\partial J}{\partial t}=\frac1{2m}\langle\nabla J,\nabla J\rangle-\lambda^je_j .$$
--   Let $v(t,p)=-\frac1m\nabla J(t,p)$ be the optimal price velocity (9). Then for all $t$, $p$ and every commodity $i$,
--
--   $$m\,\frac{\partial v_i}{\partial t}(t,p)+\tfrac12 m\,\frac{\partial}{\partial p_i}\langle v(t,\cdot),v(t,\cdot)\rangle(p)=\frac{\partial}{\partial p_i}\Big(\sum_{j=1}^n\lambda_je_j\Big)(p).$$
--
--   This nonlinear PDE is the paper's law of motion for price adjustments.
--
--   **Formalization Note** The $C^2$ assumption makes the mixed partial derivatives of $J$ commute, which the paper uses implicitly.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, p. 31, eq. (12) (from eqs. (9), (11))

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Eq. (12): if `J` is `C²` in (time, prices) and solves the HJB equation (10), then the
optimal price velocity `v = -(1/m) ∇J` satisfies
`m ∂v_i/∂t + ½ m ∇_i (v^k v_k) = ∇_i (λ^j e_j)`. -/
theorem price_velocity_evolution {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 2 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ t p, timePartial J t p =
      dot (priceGrad (J t) p) (priceGrad (J t) p) / (2 * m) - aggregateExpenditure lam e p) :
    ∀ t p i,
      m * timePartial (fun τ q => optimalVelocity m J τ q i) t p
        + (1 / 2) * m * pricePartial
            (fun q => dot (optimalVelocity m J t q) (optimalVelocity m J t q)) p i
        = pricePartial (aggregateExpenditure lam e) p i := by
  sorry

end LindgrenPriceDynamics
