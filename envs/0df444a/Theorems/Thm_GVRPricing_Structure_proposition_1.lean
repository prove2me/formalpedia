-- Prove2me | Theorems.Thm_GVRPricing_Structure_proposition_1
-- name    : GVRPricing.Structure.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:45:31.117932+00:00
-- url     : https://prove2.me/theorems/5c959250-b1f3-424f-99ac-1bad532a4a36
-- title:
--   Proposition 1 — (8) has a unique solution, and the optimal intensities satisfy $\lambda^*(n,s)\le\lambda^*$
-- statement:
--   Let $\lambda(p)$ be a regular demand function, with allowable rates $\Lambda$, revenue rate $r$ and least maximizer $\lambda^*$. Then:
--
--   1. the Hamilton–Jacobi system (8) has a solution $J(n,t)$;
--   2. the solution is unique: any two solutions agree at every stock $n$ and every time remaining $t \ge 0$;
--   3. for every solution $J$ and every $n \ge 1$, the rate $\lambda^*$ is an optimal intensity at $(n,0)$, and for every $t>0$ every optimal intensity $\lambda^*(n,t)$ satisfies
--   $$\lambda^*(n,t) \le \lambda^*.$$
--
--   Existence and uniqueness justify speaking of *the* value function $J^*(n,t)$ defined by (8); the bound says the firm never sells faster than the revenue-maximizing rate, i.e. never prices below $p^*$.
--
--   **Formalization Note** The page states "$\lambda^*(n,s)\le\lambda^*$ for all $n$ and for all $0\le s\le t$". At $s=0$ the marginal value is $J(n,0)-J(n-1,0)=0$, every maximizer of $r$ is optimal, and when $r$ is flat beyond $\lambda^*$ some of them exceed $\lambda^*$; the endpoint is therefore read as "$\lambda^*$ is an optimal intensity at $s=0$". Uniqueness is uniqueness on the domain $t\ge0$ where (8) is posed. Only the printed regular-demand hypotheses are assumed (no strict concavity, no differentiability).
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1005 (PDF 7), Proposition 1; proof p. 1017 (PDF 19)

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- Proposition 1 (Gallego–van Ryzin 1994, p. 1005). For a regular demand function:
1. the HJB system (8) has a solution;
2. any two solutions agree for every stock `n` and every time-to-go `t ≥ 0`;
3. for every solution, every `n ≥ 1`: at `t = 0` the rate `λ*` is an optimal intensity, and for
   `t > 0` every optimal intensity is at most `λ*`. -/
theorem proposition_1 (M : Model) :
    (∃ J : ℕ → ℝ → ℝ, IsHJBSolution M J) ∧
    (∀ J₁ J₂ : ℕ → ℝ → ℝ, IsHJBSolution M J₁ → IsHJBSolution M J₂ →
      ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → J₁ n t = J₂ n t) ∧
    (∀ J : ℕ → ℝ → ℝ, IsHJBSolution M J → ∀ n : ℕ, 1 ≤ n →
      IsOptimalIntensity M J n 0 M.lamStar ∧
      ∀ t : ℝ, 0 < t → ∀ ℓ : ℝ, IsOptimalIntensity M J n t ℓ → ℓ ≤ M.lamStar) := by sorry

end GVRPricing.Structure
