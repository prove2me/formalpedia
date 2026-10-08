-- Prove2me | Theorems.Thm_GVRPricing_Structure_value_and_policy_monotone
-- name    : GVRPricing.Structure.value_and_policy_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:46:16.061219+00:00
-- url     : https://prove2.me/theorems/e262dc8f-5f86-455e-aa68-1ac05800c660
-- title:
--   Theorem 1 — $J^*(n,t)$ strictly increasing and strictly concave in $n$ and $t$; optimal price falls with stock and rises with time
-- statement:
--   Let $\lambda(p)$ be a regular demand function whose revenue rate $r$ is strictly concave on the allowable rates $\Lambda$ and differentiable at every interior point of $\Lambda$, and whose least maximizer $\lambda^*$ is an interior point of $\Lambda$. Let $J(n,t)$ solve the Hamilton–Jacobi system (8), $n$ the stock and $t$ the time remaining. Then:
--
--   1. **Monotonicity.** For $t>0$, $n\mapsto J(n,t)$ is strictly increasing; for $n\ge1$, $t\mapsto J(n,t)$ is strictly increasing on $[0,\infty)$.
--   2. **Concavity.** For $n\ge1$ and $t>0$,
--   $$J(n+1,t)-J(n,t) \;<\; J(n,t)-J(n-1,t),$$
--   and for $n\ge1$, $t\mapsto J(n,t)$ is strictly concave on $[0,\infty)$.
--   3. **Optimal policy.** There is an optimal intensity $\lambda^*(n,t)$, defined for $n\ge1$ and $t>0$, such that $\lambda^*(n,t)$ is strictly increasing in $n$ and strictly decreasing in $t$, and the optimal price $p^*(n,t) = p(\lambda^*(n,t))$ is strictly decreasing in $n$ and strictly increasing in $t$.
--
--   More stock or more time yields more expected revenue, with diminishing returns; at a given time the optimal price falls as inventory grows, and for a given inventory it is higher the more time remains to sell.
--
--   **Formalization Note** As printed, Theorem 1 assumes only a regular demand function, under which $r$ is merely concave; then the monotonicity of the optimal intensity fails. For $r(\lambda)=\sqrt\lambda$ on $[0,1]$ and $r=1$ on $[1,\infty)$ (regular, $\lambda^*=1$) the solution has $J(1,t)=1-e^{-t}$ and $\lambda^*(1,t)=1$ for all $t\in(0,\ln 2]$, not strictly decreasing. For $r(\lambda)=\lambda-\lambda^2/4$ on $\Lambda=[0,1]$ (strictly concave and smooth, but $\lambda^*=1$ on the boundary) the optimal intensity is again $1$ for small $t$. The statement therefore adds the three hypotheses that the appendix proof uses: strict concavity of $r$, differentiability on the interior of $\Lambda$, and $\lambda^*$ interior (the proof uses $r'(\lambda^*)=0$). In the paper's own model, where every nonnegative price is allowable, the last condition holds whenever demand is not identically zero, because $r$ vanishes at the rate of price $0$. The exponential and linear demand examples satisfy all three. Strict statements in $n$ are for $t>0$ (at $t=0$ all $J(n,0)=0$), and the optimal intensity is required only for $n\ge1$, $t>0$, where (8) is posed. $J$ is any solution of (8); by Proposition 1 there is exactly one.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1005 (PDF 7), Theorem 1; proof pp. 1017–1018 (PDF 19–20)

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

namespace GVRPricing.Structure

/-- Theorem 1 (Gallego–van Ryzin 1994, p. 1005), for the solution `J` of the HJB system (8), with
`t` the time remaining, under the added hypotheses (used by the appendix proof) that `r` is
strictly concave on `Λ`, differentiable on the interior of `Λ`, and that `λ*` lies in the
interior of `Λ`:
1. `J(n, t)` is strictly increasing in `n` for `t > 0`, and in `t ≥ 0` for `n ≥ 1`;
2. `J(n, t)` is strictly concave in `n` (strictly decreasing increments, `t > 0`) and in
   `t ∈ [0, ∞)` (`n ≥ 1`);
3. there is an optimal intensity `ℓ(n, t)` (`n ≥ 1`, `t > 0`) that is strictly increasing in `n`
   and strictly decreasing in `t`, whose price `p(ℓ(n, t))` is strictly decreasing in `n` and
   strictly increasing in `t`. -/
theorem value_and_policy_monotone (M : Model) (hstrict : StrictConcaveOn ℝ M.Λ M.r)
    (hdiff : ∀ x ∈ interior M.Λ, DifferentiableAt ℝ M.r x)
    (hint : M.lamStar ∈ interior M.Λ)
    (J : ℕ → ℝ → ℝ) (hJ : IsHJBSolution M J) :
    (∀ t : ℝ, 0 < t → StrictMono (fun n : ℕ => J n t)) ∧
    (∀ n : ℕ, 1 ≤ n → StrictMonoOn (J n) (Set.Ici 0)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → J (n + 1) t - J n t < J n t - J (n - 1) t) ∧
    (∀ n : ℕ, 1 ≤ n → StrictConcaveOn ℝ (Set.Ici 0) (J n)) ∧
    ∃ ℓ : ℕ → ℝ → ℝ,
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → IsOptimalIntensity M J n t (ℓ n t)) ∧
      (∀ t : ℝ, 0 < t → StrictMonoOn (fun n : ℕ => ℓ n t) (Set.Ici 1)) ∧
      (∀ n : ℕ, 1 ≤ n → StrictAntiOn (ℓ n) (Set.Ioi 0)) ∧
      (∀ t : ℝ, 0 < t → StrictAntiOn (fun n : ℕ => M.p (ℓ n t)) (Set.Ici 1)) ∧
      (∀ n : ℕ, 1 ≤ n → StrictMonoOn (fun t : ℝ => M.p (ℓ n t)) (Set.Ioi 0)) := by sorry

end GVRPricing.Structure
