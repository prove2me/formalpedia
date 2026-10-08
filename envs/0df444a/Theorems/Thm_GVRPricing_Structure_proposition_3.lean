-- Prove2me | Theorems.Thm_GVRPricing_Structure_proposition_3
-- name    : GVRPricing.Structure.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:46:25.654381+00:00
-- url     : https://prove2.me/theorems/896939b5-adf1-4838-8d6a-7c75c067a183
-- title:
--   Proposition 3 — for $\lambda(p)=ae^{-p}$, $\lambda^*(n,t)\le\lambda^D(n,t)$ and $p^*(n,t)\ge p^D(n,t)$
-- statement:
--   Consider exponential demand $\lambda(p) = ae^{-p}$, $a>0$, with allowable rates $\Lambda=[0,a]$ and inverse demand $p(\lambda)=\log(a/\lambda)$. Let $J$ solve the Hamilton–Jacobi system (8), and let $\lambda^D(n,t) = \min\{\lambda^*, n/t\}$ be the optimal rate of the deterministic problem, with price $p^D(n,t) = p(\lambda^D(n,t))$. Then for every stock $n\ge1$, every time remaining $t>0$ and every optimal intensity $\lambda^*(n,t)$ at $(n,t)$,
--   $$\lambda^*(n,t) \le \lambda^D(n,t) \qquad\text{and}\qquad p^*(n,t) = p\big(\lambda^*(n,t)\big) \ge p^D(n,t).$$
--
--   Under exponential demand the stochastic optimal policy always sells more slowly, at a higher price, than its deterministic counterpart; the paper notes that this comparison fails for other demand functions such as $r(\lambda) = 1-(\lambda-1)^2$.
--
--   **Formalization Note** The page states the result for all $n\ge0$ and $t\ge0$. At $n=0$ there is no optimal intensity in (8), and at $t=0$ the rate $n/t$ is undefined, so the statement is made for $n\ge1$ and $t>0$, where both sides are defined. $\lambda^D$ is defined locally (it is Proposition 2's object, formalized in the first mission of this series).
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1009 (PDF 11), §3.5, Proposition 3

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- Proposition 3 (Gallego–van Ryzin 1994, §3.5, p. 1009), exponential demand `λ(p) = a e^{−p}`
(allowable rates `Λ = [0, a]`, inverse demand `p(λ) = log(a / λ)`): for a solution `J` of (8),
`n ≥ 1` and time-to-go `t > 0`, every optimal intensity `ℓ` at `(n, t)` is at most the
deterministic rate `λ^D(n, t) = min {λ*, n / t}`, and its price is at least `p^D(n, t) = p(λ^D(n, t))`. -/
theorem proposition_3 (M : Model) (a : ℝ) (ha : 0 < a)
    (hΛ : M.Λ = Set.Icc 0 a) (hp : ∀ x ∈ M.Λ, x ≠ 0 → M.p x = Real.log (a / x))
    (J : ℕ → ℝ → ℝ) (hJ : IsHJBSolution M J) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t)
    (ℓ : ℝ) (hℓ : IsOptimalIntensity M J n t ℓ) :
    ℓ ≤ M.detRate n t ∧ M.p (M.detRate n t) ≤ M.p ℓ := by sorry

end GVRPricing.Structure
