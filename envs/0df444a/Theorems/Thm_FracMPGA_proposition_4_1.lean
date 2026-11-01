-- Prove2me | Theorems.Thm_FracMPGA_proposition_4_1
-- name    : FracMPGA.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:42:02.142986+00:00
-- url     : https://prove2.me/theorems/771b8c27-e707-44d1-8a9c-56879669a408
-- title:
--   Proposition 4.1 — a fixed point of the proximity steps is a critical point
-- statement:
--   Let $(x^\star,y^\star)\in\Omega\times\mathbb R^n$ and $\alpha_0,\alpha_1,\dots,\alpha_N>0$ satisfy
--   $$
--   y^\star=\operatorname{prox}_{\alpha_0g^*}(y^\star+\alpha_0x^\star),\tag{17}
--   $$
--   $$
--   x_i^\star\in\operatorname{prox}_{\alpha_if_i}\big(x_i^\star-\alpha_i\nabla_ih(x^\star)+\alpha_iQ(x^\star,y^\star)y_i^\star\big),\quad i=1,\dots,N.\tag{18}
--   $$
--   Then $x^\star$ is a critical point of $F$ with $y^\star\in\partial g(x^\star)$ and $(x^\star,y^\star)\in\operatorname{dom}Q$; if moreover $g^*$ is continuous on $\operatorname{dom}g^*$, then $(x^\star,y^\star)$ is a stationary point of $Q$, $0\in\hat\partial Q(x^\star,y^\star)$.
--
--   It motivates the algorithm: a point left unchanged by every proximity step of MPGA is critical.
--
--   **Formalization Note** The step sizes are indexed by $\{0,\dots,N\}$, $\alpha_0$ for the $y$-step. In (18), $Q(x^\star,y^\star)$ enters as a real number; (17) already forces $(x^\star,y^\star)\in\operatorname{dom}Q$.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
--   - encoding: y = prox_{αg*}(·) and x_i(α) ∈ prox_{αf_i}(·) → membership in the argmin set proxSet α φ v; reason: the prox of the convex g* is a single point, so membership and equality agree; the prox of f_i is set-valued as on p.13
--   - encoding: Q(x⋆, y⋆) in (18) → (Q x⋆ y⋆).toReal inside xStepInput; reason: (17) forces (x⋆, y⋆) ∈ dom(Q), where this is Q(x⋆, y⋆)
--   - reading: 'and hence (x⋆, y⋆) ∈ dom(Q) is a stationary point of Q if g* is continuous on dom(g*)' → (x⋆, y⋆) ∈ dom(Q) unconditionally, stationarity under the continuity of g*; reason: the sentence admits both scopes for the condition; the unconditional membership is the stronger reading and follows from y⋆ ∈ ∂g(x⋆) and g(x⋆) > 0
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.13, Proposition 4.1

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracMPGA_proxSet
import Definitions.Def_FracMPGA_liftedRatio
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1
import Definitions.Def_FracMPGA_IsCritical
import Definitions.Def_FracMPGA_IsMPGARun
open NonconvexSplitting.Shared

namespace FracMPGA

/-- **Proposition 4.1** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.13: if `(x⋆, y⋆) ∈ Ω × ℝⁿ`
satisfies
`y⋆ = prox_{α₀g*}(y⋆ + α₀x⋆)` (17) and
`x⋆_i ∈ prox_{α_i f_i}(x⋆_i − α_i∇_i h(x⋆) + α_i Q(x⋆, y⋆) y⋆_i)`, `i ∈ ℕ_N` (18),
for some `α_i > 0`, `i ∈ ℕ⁰_N`, then `x⋆` is a critical point of `F` with `y⋆ ∈ ∂g(x⋆)`, and hence
`(x⋆, y⋆) ∈ dom(Q)` is a stationary point of `Q` if `g*` is continuous on `dom(g*)`.

**Formalization Note** Assumption 1 is `hA1`. The step sizes are `α : Fin (N+1) → ℝ`, `α 0`
being `α₀` and `α r.succ` the step of paper block `r + 1`. (17) is membership in the prox set
(the prox of the convex `g*` is a single point, so membership and equality agree). In (18),
`Q(x⋆, y⋆)` enters as a real number through `xStepInput`; (17) forces `(x⋆, y⋆) ∈ dom(Q)`.
`(x⋆, y⋆) ∈ dom(Q)` is asserted unconditionally, stationarity under the continuity of `g*`. -/
theorem proposition_4_1 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (xs ys : Vec n)
    (hΩ : P.g xs ≠ 0) (α : Fin (N + 1) → ℝ) (hα : ∀ i, 0 < α i)
    (h17 : ys ∈ proxSet (α 0) (ConvexOptimization.fenchelConjugate P.g) (ys + α 0 • xs))
    (h18 : ∀ r : Fin N,
      P.block xs r ∈ proxSet (α r.succ) (P.fb r) (P.xStepInput xs ys r (α r.succ))) :
    IsCritical P xs ∧ ys ∈ ProxAlg.FixedPoint.subdifferential (fun z => (P.g z : EReal)) xs ∧ P.Q xs ys ≠ ⊤ ∧
      (ContinuousOn (ConvexOptimization.fenchelConjugate P.g)
          {y | ConvexOptimization.fenchelConjugate P.g y ≠ ⊤} →
        IsRegularSubgrad P.Qp (pair xs ys) 0) := by sorry

end FracMPGA
