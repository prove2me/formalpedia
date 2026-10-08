-- Prove2me | Theorems.Thm_GVRPricing_Structure_first_order_condition
-- name    : GVRPricing.Structure.first_order_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:45:47.44373+00:00
-- url     : https://prove2.me/theorems/83266f8c-0a89-45e3-8b14-fc8e4897ef8a
-- title:
--   Eq. (26) — $J(n,t) = J(n-1,t) + r'(\lambda^*(n,t)) > J(n-1,t)$ for $t>0$
-- statement:
--   Let $\lambda(p)$ be a regular demand function whose revenue rate $r$ is moreover strictly concave on $\Lambda$ and differentiable at every interior point of $\Lambda$, and whose least maximizer $\lambda^*$ is an interior point of $\Lambda$. Let $J$ solve (8), let $n \ge 1$ and $t > 0$, and let $\lambda^*(n,t)$ be an optimal intensity at $(n,t)$. Then $\lambda^*(n,t)$ is an interior point of $\Lambda$, and
--   $$J(n,t) = J(n-1,t) + r'\big(\lambda^*(n,t)\big) > J(n-1,t).$$
--
--   This first-order condition (26) links the marginal value of an item to the marginal revenue at the optimal rate; it opens the paper's proof of Theorem 1.
--
--   **Formalization Note** The three hypotheses beyond the printed regular-demand assumptions are those the appendix proof uses (it differentiates $r$ and $r'$, and uses $r'(\lambda^*)=0$); they are added to this item and disclosed. The conclusion is stated as `HasDerivAt r (J n t - J (n-1) t) ℓ` together with positivity of the marginal value.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1017 (PDF 19), Appendix, Proof of Theorem 1, eq. (26)

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- Eq. (26) (Gallego–van Ryzin 1994, Appendix, Proof of Theorem 1, p. 1017), under the added
hypotheses that `r` is strictly concave on `Λ`, differentiable on the interior of `Λ`, and that
`λ*` lies in the interior of `Λ`: for a solution `J` of (8), `n ≥ 1`, `t > 0` and any optimal
intensity `ℓ` at `(n, t)`, the rate `ℓ` is interior, the marginal value
`J(n, t) − J(n − 1, t)` is positive, and it equals `r′(ℓ)`. -/
theorem first_order_condition (M : Model) (hstrict : StrictConcaveOn ℝ M.Λ M.r)
    (hdiff : ∀ x ∈ interior M.Λ, DifferentiableAt ℝ M.r x)
    (hint : M.lamStar ∈ interior M.Λ)
    (J : ℕ → ℝ → ℝ) (hJ : IsHJBSolution M J) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t)
    (ℓ : ℝ) (hℓ : IsOptimalIntensity M J n t ℓ) :
    ℓ ∈ interior M.Λ ∧ 0 < J n t - J (n - 1) t ∧ HasDerivAt M.r (J n t - J (n - 1) t) ℓ := by sorry

end GVRPricing.Structure
