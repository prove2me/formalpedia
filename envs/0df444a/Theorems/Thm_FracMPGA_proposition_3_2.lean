-- Prove2me | Theorems.Thm_FracMPGA_proposition_3_2
-- name    : FracMPGA.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:41.022139+00:00
-- url     : https://prove2.me/theorems/fab9afa4-4d99-4acc-91e6-0c258d8576cc
-- title:
--   Proposition 3.2 — critical points of $F$ correspond to stationary points of $Q$
-- statement:
--   Under the standing assumptions on problem (1), let $(x^\star,y^\star)\in\operatorname{dom}Q$ and suppose that the conjugate $g^*$ is continuous on $\operatorname{dom}g^*$. Then
--   $$
--   x^\star\text{ is a critical point of }F\text{ with }F(x^\star)y^\star\in F(x^\star)\,\partial g(x^\star)\iff 0\in\hat\partial Q(x^\star,y^\star),
--   $$
--   that is, $(x^\star,y^\star)$ is a stationary point of $Q$, with $\hat\partial$ the Fréchet subdifferential on the Euclidean product $\mathbb R^n\times\mathbb R^n$.
--
--   The equivalence lets the algorithms, which work on the lifted objective $Q$, certify criticality for the original ratio $F$.
--
--   **Formalization Note** $F(x^\star)\,\partial g(x^\star)$ is the set $\partial g(x^\star)$ scaled by the number $F(x^\star)$, so the side condition is vacuous when $F(x^\star)=0$, as on the page.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §3, p.11, Proposition 3.2

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracMPGA_liftedRatio
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1
import Definitions.Def_FracMPGA_IsCritical
open NonconvexSplitting.Shared
open scoped Pointwise

namespace FracMPGA

/-- **Proposition 3.2** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.11: let `(x⋆, y⋆) ∈ dom(Q)` and
let `g*` be continuous on `dom(g*)`. Then `x⋆` is a critical point of `F` with
`F(x⋆) y⋆ ∈ F(x⋆) ∂g(x⋆)` if and only if `(x⋆, y⋆)` is a stationary point of `Q`, i.e.
`0 ∈ ∂̂Q(x⋆, y⋆)`.

**Formalization Note** Assumption 1 (blanket, p.2) is the hypothesis `hA1`. `F(x⋆) ∂g(x⋆)` is the
pointwise scaling of the set `∂g(x⋆)` by the real number `F(x⋆)`, so the side condition is vacuous
when `F(x⋆) = 0`, as on the page. `∂̂Q` is the Fréchet subdifferential of `Q` on the Euclidean
product `ℝⁿ × ℝⁿ` (`IsRegularSubgrad P.Qp`). -/
theorem proposition_3_2 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (xs ys : Vec n)
    (hdom : P.Q xs ys ≠ ⊤)
    (hcont : ContinuousOn (ConvexOptimization.fenchelConjugate P.g)
      {y | ConvexOptimization.fenchelConjugate P.g y ≠ ⊤}) :
    (IsCritical P xs ∧
      (P.F xs).toReal • ys ∈ (P.F xs).toReal • ProxAlg.FixedPoint.subdifferential (fun z => (P.g z : EReal)) xs) ↔
      IsRegularSubgrad P.Qp (pair xs ys) 0 := by sorry

end FracMPGA
