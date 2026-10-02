-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_lyapunov_derivative
-- name    : LindgrenPriceDynamics.lyapunov_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T18:38:38.481607+00:00
-- url     : https://prove2.me/theorems/805fac3e-032d-4385-a1b1-8bfa7b998999
-- title:
--   Derivative of the value function along optimal prices: $dJ/ds=\lambda^je_j-\frac32 mv^iv_i$
-- statement:
--   Let $m>0$, weights $\lambda_j$ and expenditure functions $e_j$. Let $J(s,p)$ be continuously differentiable in $(s,p)$ and solve the time-inverted HJB equation
--   $$\frac{\partial J}{\partial s}=-\frac1{2m}\langle\nabla J,\nabla J\rangle+\lambda^je_j .$$
--   Let $p(s)$ be a price path following the optimal policy, $\dot p(s)=v(s):=-\frac1m\nabla J(s,p(s))$ for all $s$. Then $s\mapsto J(s,p(s))$ is differentiable with
--
--   $$\frac{d}{ds}J(s,p(s))=\sum_{j=1}^n\lambda_je_j(p(s))-\tfrac32\,m\,\langle v(s),v(s)\rangle .$$
--
--   This identity underlies the paper's Lyapunov stability criterion.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, p. 31, eqs. (17)–(19)

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Eq. (19): if `J` is `C¹` and solves the time-inverted HJB equation
`∂J/∂s = -(1/2m) ∇^i J ∇_i J + λ^j e_j`, and the price path follows the optimal policy
`dp/ds = v = -(1/m) ∇J`, then `dJ/ds = λ^j e_j - (3/2) m v^i v_i` along the path. -/
theorem lyapunov_derivative {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 1 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ s p, timePartial J s p =
      -(dot (priceGrad (J s) p) (priceGrad (J s) p)) / (2 * m) + aggregateExpenditure lam e p)
    (p : ℝ → Fin l → ℝ) (hp : ∀ s, HasDerivAt p (optimalVelocity m J s (p s)) s) :
    ∀ s, HasDerivAt (fun s => J s (p s))
      (aggregateExpenditure lam e (p s)
        - (3 / 2) * m * dot (optimalVelocity m J s (p s)) (optimalVelocity m J s (p s))) s := by
  sorry

end LindgrenPriceDynamics
