-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_lyapunov_stability_condition
-- name    : LindgrenPriceDynamics.lyapunov_stability_condition
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T18:41:15.910666+00:00
-- url     : https://prove2.me/theorems/1cdf8515-d5a4-4629-b3dc-ba19cd558d6e
-- title:
--   Lyapunov stability condition: $J$ decreases along optimal prices when $\lambda^je_j<\frac32 mv^iv_i$
-- statement:
--   Let $m>0$, weights $\lambda_j$, expenditure functions $e_j$, and let $J(s,p)$ be continuously differentiable and solve the time-inverted HJB equation
--   $$\frac{\partial J}{\partial s}=-\frac1{2m}\langle\nabla J,\nabla J\rangle+\lambda^je_j .$$
--   Let the price path satisfy $\dot p(s)=v(s):=-\frac1m\nabla J(s,p(s))$ for all $s$. Suppose that on an interval $[t,T]$ price adjustments are large enough:
--
--   $$\sum_{j=1}^n\lambda_je_j(p(s))<\tfrac32\,m\,\langle v(s),v(s)\rangle\qquad\text{for all } s\in[t,T].$$
--
--   Then:
--   1. $s\mapsto J(s,p(s))$ is strictly decreasing on $[t,T]$;
--   2. if in addition $J(T,p(T))=0$ (the value function vanishes at the equilibrium time $T$), then $J(s,p(s))>0$ for all $s\in[t,T)$.
--
--   This is the paper's conclusion that the value function acts as a Lyapunov function, and the equilibrium is approached, as long as the squared price velocity is large compared with aggregate expenditure.
--
--   **Formalization Note** The paper's informal notion of 'stability' is rendered as strict decrease of $J$ along the optimal path together with positivity before the terminal time; the HJB equation and the optimal feedback law are hypotheses.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, pp. 31–32, Section 3 'Conditions for Lyapunov Stability of the Economy', eq. (19) and the following paragraph

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Section 3 (Lyapunov stability, eq. (19) and the following paragraph): under the
hypotheses of eq. (19), if on `[t, T]` the price velocity is large enough,
`λ^j e_j < (3/2) m v^i v_i`, then the value function `J` is strictly decreasing along the
optimal price path on `[t, T]`; and if moreover `J` vanishes at the equilibrium time `T`,
it is strictly positive on `[t, T)`. -/
theorem lyapunov_stability_condition {n l : ℕ} (m : ℝ) (hm : 0 < m) (lam : Fin n → ℝ)
    (e : Fin n → (Fin l → ℝ) → ℝ) (J : ℝ → (Fin l → ℝ) → ℝ)
    (hJ : ContDiff ℝ 1 (fun x : ℝ × (Fin l → ℝ) => J x.1 x.2))
    (hHJB : ∀ s p, timePartial J s p =
      -(dot (priceGrad (J s) p) (priceGrad (J s) p)) / (2 * m) + aggregateExpenditure lam e p)
    (p : ℝ → Fin l → ℝ) (hp : ∀ s, HasDerivAt p (optimalVelocity m J s (p s)) s)
    (t T : ℝ)
    (hlarge : ∀ s ∈ Set.Icc t T, aggregateExpenditure lam e (p s)
      < (3 / 2) * m * dot (optimalVelocity m J s (p s)) (optimalVelocity m J s (p s))) :
    StrictAntiOn (fun s => J s (p s)) (Set.Icc t T) ∧
      (J T (p T) = 0 → ∀ s ∈ Set.Ico t T, 0 < J s (p s)) := by
  sorry

end LindgrenPriceDynamics
