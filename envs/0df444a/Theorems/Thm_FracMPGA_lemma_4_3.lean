-- Prove2me | Theorems.Thm_FracMPGA_lemma_4_3
-- name    : FracMPGA.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:47.505204+00:00
-- url     : https://prove2.me/theorems/15854437-417a-4e1d-8d75-47b0f4b7b1ab
-- title:
--   Lemma 4.3 — the proximity step of $g^*$ in $y$
-- statement:
--   Let $(x,y)\in\mathbb R^n\times\mathbb R^n$, $\alpha>0$ and $y^+(\alpha)=\operatorname{prox}_{\alpha g^*}(y+\alpha x)$. Then
--
--   1. $\dfrac{y-y^+(\alpha)}{\alpha}+x\in\partial g^*(y^+(\alpha))$;
--   2. $\eta(x,y)+\dfrac{\|y-y^+(\alpha)\|_2^2}{\alpha}\le\eta(x,y^+(\alpha))\le g(x)$;
--   3. if $(x,y)\in\operatorname{dom}Q$, then $(x,y^+(\alpha))\in\operatorname{dom}Q$ and, for every $c\in[Q(x,y),+\infty)$,
--   $$
--   \zeta(x)+\frac c\alpha\|y-y^+(\alpha)\|_2^2\le c\,\eta(x,y^+(\alpha)).\tag{21}
--   $$
--
--   This is the descent property of Step 2-Y of the algorithm.
--
--   **Formalization Note** Item 2 is stated in the extended reals, where $\eta(x,y)=-\infty$ when $y\notin\operatorname{dom}g^*$; (21) is stated in the extended reals with $c$ real.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
--   - encoding: y = prox_{αg*}(·) and x_i(α) ∈ prox_{αf_i}(·) → membership in the argmin set proxSet α φ v; reason: the prox of the convex g* is a single point, so membership and equality agree; the prox of f_i is set-valued as on p.13
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.15, Lemma 4.3

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_FracMPGA_proxSet
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1

namespace FracMPGA

/-- **Lemma 4.3** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.15: let `(x, y) ∈ ℝⁿ × ℝⁿ`, `α > 0`
and `y⁺(α) = prox_{αg*}(y + αx)`. Then
(i) `(y − y⁺(α))/α + x ∈ ∂g*(y⁺(α))`;
(ii) `η(x, y) + ‖y − y⁺(α)‖₂²/α ≤ η(x, y⁺(α)) ≤ g(x)`;
(iii) if `(x, y) ∈ dom(Q)`, then `(x, y⁺(α)) ∈ dom(Q)`, and
`ζ(x) + (c/α)‖y − y⁺(α)‖₂² ≤ c η(x, y⁺(α))` (21) holds for any `c ∈ [Q(x, y), +∞)`.

**Formalization Note** Assumption 1 is `hA1`. `y⁺(α)` is any element `yp` of the prox set (a
single point, `g*` being convex). (ii) is stated in `EReal`, where `η(x, y) = −∞` when
`y ∉ dom(g*)`; (21) is stated in `EReal` with `c` real. -/
theorem lemma_4_3 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (x y : Vec n) (α : ℝ)
    (hα : 0 < α) (yp : Vec n)
    (hyp : yp ∈ proxSet α (ConvexOptimization.fenchelConjugate P.g) (y + α • x)) :
    α⁻¹ • (y - yp) + x ∈ ProxAlg.FixedPoint.subdifferential (ConvexOptimization.fenchelConjugate P.g) yp ∧
    (P.eta x y + ((‖y - yp‖ ^ 2 / α : ℝ) : EReal) ≤ P.eta x yp ∧
      P.eta x yp ≤ (P.g x : EReal)) ∧
    (P.Q x y ≠ ⊤ → P.Q x yp ≠ ⊤ ∧ ∀ c : ℝ, P.Q x y ≤ (c : EReal) →
      P.zeta x + ((c / α * ‖y - yp‖ ^ 2 : ℝ) : EReal) ≤ (c : EReal) * P.eta x yp) := by sorry

end FracMPGA
