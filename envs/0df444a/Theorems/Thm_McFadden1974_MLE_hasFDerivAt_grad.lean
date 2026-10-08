-- Prove2me | Theorems.Thm_McFadden1974_MLE_hasFDerivAt_grad
-- name    : McFadden1974.MLE.hasFDerivAt_grad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:02.92243+00:00
-- url     : https://prove2.me/theorems/b3ac5f1d-be05-4ae9-8c3f-0d338b284769
-- title:
--   Equation (20) — the Hessian of the conditional logit log-likelihood
-- statement:
--   In the conditional logit model, the gradient field $\theta \mapsto \partial L/\partial\theta$ of Equation (19) is differentiable at every $\theta$, and its derivative is
--   $$\frac{\partial^2 L}{\partial\theta\,\partial\theta'} = -\sum_{n=1}^N R_n \sum_{j=1}^{J_n} (z_{jn} - \bar z_n)' P_{jn} (z_{jn} - \bar z_n), \qquad \bar z_n = \sum_{i=1}^{J_n} z_{in} P_{in},$$
--   acting on $\gamma \in \mathbb{R}^K$ as $\gamma \mapsto -\sum_n R_n \sum_j P_{jn} \langle z_{jn} - \bar z_n, \gamma\rangle (z_{jn} - \bar z_n)$.
--
--   The Hessian is minus a weighted moment matrix of the centred attributes, which underlies the concavity of $L$ and the asymptotic covariance of the estimator.
--
--   **Formalization Note** The second derivative is stated as the Fréchet derivative of the vector field of Equation (19).
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 115 (PDF p. 11), Equation (20)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Equation (20)** (McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 115, PDF p. 11).

The gradient field `θ ↦ ∂L/∂θ` of (19) is differentiable at every `θ`, and its derivative, the
Hessian `∂²L/∂θ∂θ'`, is the linear map
`γ ↦ −∑_{n=1}^N R_n ∑_{j=1}^{J_n} P_jn ⟨z_jn − z̄_n, γ⟩ (z_jn − z̄_n)` (`Data.hess`), with
`z̄_n = ∑_i z_in P_in`.

**Formalization Note.** The second derivative is stated as the Fréchet derivative of the gradient
vector field `Data.grad`, whose identification with `∇L` is Equation (19). -/
theorem hasFDerivAt_grad
    {K : ℕ} (d : Data K) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt d.grad (d.hess θ) θ := by sorry

end McFadden1974.MLE
