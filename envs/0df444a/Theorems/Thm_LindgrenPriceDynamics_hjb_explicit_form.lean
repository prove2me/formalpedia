-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_hjb_explicit_form
-- name    : LindgrenPriceDynamics.hjb_explicit_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T18:17:49.831095+00:00
-- url     : https://prove2.me/theorems/76040940-7997-481d-9f56-1c20eb176b9d
-- title:
--   Explicit Hamilton–Jacobi–Bellman equation: $\partial_tJ=\frac1{2m}|\nabla J|^2-\lambda^je_j$
-- statement:
--   Let $m>0$, weights $\lambda_1,\dots,\lambda_n$, expenditure functions $e_1,\dots,e_n:\mathbb R^l\to\mathbb R$, and $J(t,p)$ a function of time and prices. Suppose $J$ satisfies the Hamilton–Jacobi–Bellman equation in its minimization form, with the Hamiltonian (8):
--   $$-\frac{\partial J}{\partial t}(t,p)=\inf_{v\in\mathbb R^l}\Big(\tfrac12 m\langle v,v\rangle+\lambda^je_j(p)+\langle\nabla J(t,p),v\rangle\Big)\quad\text{for all }t,p .$$
--   Then for all $t,p$,
--
--   $$\frac{\partial J}{\partial t}(t,p)=\frac1{2m}\,\langle\nabla J(t,p),\nabla J(t,p)\rangle-\sum_{j=1}^n\lambda_je_j(p).$$
--
--   This is eq. (10), the PDE for the value function of the price-adjustment problem.
--
--   **Formalization Note** The HJB equation itself is taken as a hypothesis, as in the paper; the value function is not defined from the cost functional.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, p. 30, eq. (10) (with eqs. (8)–(9))

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Eq. (10): if `J` satisfies the Hamilton–Jacobi–Bellman equation
`-∂J/∂t = min_v H` with the Hamiltonian (8), then
`∂J/∂t = (1/2m) ∇^i J ∇_i J - λ^j e_j`. -/
theorem hjb_explicit_form {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hHJB : ∀ t p, -timePartial J t p =
      ⨅ v : Fin l → ℝ, hamiltonian m (aggregateExpenditure lam e p) (priceGrad (J t) p) v) :
    ∀ t p, timePartial J t p =
      dot (priceGrad (J t) p) (priceGrad (J t) p) / (2 * m) - aggregateExpenditure lam e p := by
  sorry

end LindgrenPriceDynamics
