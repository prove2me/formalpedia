-- Prove2me | Theorems.Thm_GVRPricing_Structure_base_case
-- name    : GVRPricing.Structure.base_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:45:59.73915+00:00
-- url     : https://prove2.me/theorems/6d738bee-0db4-41f8-9e6f-ef7322e1a7ac
-- title:
--   Proof of Theorem 1, case $n=1$ — $\lambda^*(1,t)$ strictly decreasing, $J(1,t)$ strictly concave in $t$
-- statement:
--   Let $\lambda(p)$ be a regular demand function whose revenue rate $r$ is strictly concave on $\Lambda$ and differentiable at every interior point of $\Lambda$, with $\lambda^*$ interior to $\Lambda$. Let $J$ solve (8), and for each time remaining $t>0$ let $\lambda^*(1,t)$ be an optimal intensity at $(1,t)$. Then
--
--   1. $t\mapsto\lambda^*(1,t)$ is strictly decreasing on $(0,\infty)$;
--   2. $t\mapsto J(1,t)$ is strictly concave on $[0,\infty)$;
--   3. for every $t>0$,
--   $$\frac{\partial J(1,t)}{\partial t} = r\big(\lambda^*(1,t)\big) - \lambda^*(1,t)\,J(1,t).$$
--
--   This is the base case of the induction on $n$ by which the paper proves Theorem 1: with a single item, the firm prices higher the more time remains, and the value of the item grows concavely with time.
--
--   **Formalization Note** The page also displays $\partial J(1,t)/\partial t = r''(\lambda^*(1,t))\lambda^{*\prime}(1,t)$ and $\partial^2J(1,t)/\partial t^2 = -\lambda^*(1,t)\,\partial J(1,t)/\partial t$; these presuppose second derivatives of $r$ and $J$ that the hypotheses do not provide and are intermediate steps, so they are not stated; the conclusions they serve (items 1 and 2) are. The hypotheses beyond regular demand are those of eq. (26) and are disclosed there.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1017 (PDF 19), Appendix, Proof of Theorem 1, the case n = 1

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- The case `n = 1` of the proof of Theorem 1 (Gallego–van Ryzin 1994, Appendix, p. 1017), under
the added hypotheses that `r` is strictly concave on `Λ`, differentiable on the interior of `Λ`,
and that `λ*` lies in the interior of `Λ`. For a solution `J` of (8) and any choice `ℓ(t)` of an
optimal intensity at `(1, t)` for each time-to-go `t > 0`:
1. `t ↦ ℓ(t)` is strictly decreasing on `(0, ∞)`;
2. `J(1, ·)` is strictly concave on `[0, ∞)`;
3. `∂J(1, t)/∂t = r(ℓ(t)) − ℓ(t) J(1, t)` for `t > 0`. -/
theorem base_case (M : Model) (hstrict : StrictConcaveOn ℝ M.Λ M.r)
    (hdiff : ∀ x ∈ interior M.Λ, DifferentiableAt ℝ M.r x)
    (hint : M.lamStar ∈ interior M.Λ)
    (J : ℕ → ℝ → ℝ) (hJ : IsHJBSolution M J) (ℓ : ℝ → ℝ)
    (hℓ : ∀ t : ℝ, 0 < t → IsOptimalIntensity M J 1 t (ℓ t)) :
    StrictAntiOn ℓ (Set.Ioi 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) (J 1) ∧
    ∀ t : ℝ, 0 < t → HasDerivAt (J 1) (M.r (ℓ t) - ℓ t * J 1 t) t := by sorry

end GVRPricing.Structure
