-- Prove2me | Theorems.Thm_GVRPricing_Structure_exponential_closed_form
-- name    : GVRPricing.Structure.exponential_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:46:24.674701+00:00
-- url     : https://prove2.me/theorems/3974df01-0e16-4025-86fb-6960cecec400
-- title:
--   §2.3, eqs. (9)–(10) — for $\lambda(p)=ae^{-p}$, $J^*(n,t)=\log\sum_{i=0}^n(\lambda^*t)^i/i!$ and $p^*(n,t)=J^*(n,t)-J^*(n-1,t)+1$
-- statement:
--   Consider exponential demand $\lambda(p) = a e^{-p}$ with $a>0$: the allowable rates are $\Lambda = [0,a]$ and the inverse demand is $p(\lambda) = \log(a/\lambda)$ for $0<\lambda\le a$, so $r(\lambda) = \lambda\log(a/\lambda)$. Then the least maximizer of $r$ is $\lambda^* = a/e$, with $p^* = p(\lambda^*) = 1$; the function
--   $$J(n,t) = \log\Big(\sum_{i=0}^{n} \frac{(\lambda^* t)^i}{i!}\Big)$$
--   for $t\ge0$ solves the Hamilton–Jacobi system (8); and for every $n\ge1$ and $t>0$ every optimal intensity $\lambda^*(n,t)$ has price
--   $$p^*(n,t) = p\big(\lambda^*(n,t)\big) = J(n,t) - J(n-1,t) + 1.$$
--
--   This closed form is one of the few exactly solvable cases of the problem and is the basis of the paper's numerical comparison of heuristics and of Proposition 3.
--
--   **Formalization Note** The paper treats $\lambda(p)=ae^{-\alpha p}$ and reduces to $\alpha=1$ by changing price units $p'\leftarrow\alpha p$; the statement is made for $\alpha=1$. The model is any regular demand function with $\Lambda=[0,a]$ and $p(\lambda)=\log(a/\lambda)$ on $(0,a]$; the value of $\lambda^*$ is a conclusion, not an assumption. By Proposition 1 this $J$ is the unique solution.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1005 (PDF 7), §2.3, eqs. (9)–(10)

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- §2.3, eqs. (9)–(10) (Gallego–van Ryzin 1994, p. 1005), exponential demand `λ(p) = a e^{−p}`
(price units normalized so that `α = 1`): allowable rates `Λ = [0, a]`, inverse demand
`p(λ) = log(a / λ)`. Then `λ* = a / e`, `p* = 1`, the function
`J(n, t) = log (∑_{i=0}^{n} (λ* t)^i / i!)` solves (8), and for `n ≥ 1`, `t > 0` every optimal
intensity `ℓ` at `(n, t)` has price `p(ℓ) = J(n, t) − J(n − 1, t) + 1`. -/
theorem exponential_closed_form (M : Model) (a : ℝ) (ha : 0 < a)
    (hΛ : M.Λ = Set.Icc 0 a) (hp : ∀ x ∈ M.Λ, x ≠ 0 → M.p x = Real.log (a / x))
    (J : ℕ → ℝ → ℝ)
    (hJdef : ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      J n t = Real.log (∑ i ∈ Finset.range (n + 1), (M.lamStar * t) ^ i / (i.factorial : ℝ))) :
    M.lamStar = a / Real.exp 1 ∧ M.pStar = 1 ∧ IsHJBSolution M J ∧
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → ∀ ℓ : ℝ, IsOptimalIntensity M J n t ℓ →
      M.p ℓ = J n t - J (n - 1) t + 1 := by sorry

end GVRPricing.Structure
