-- Prove2me | Theorems.Thm_FracMPGA_lemma_4_4
-- name    : FracMPGA.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:43.180523+00:00
-- url     : https://prove2.me/theorems/b329b9d7-5b3a-444a-8d30-073f60e8efee
-- title:
--   Lemma 4.4 — the $y$-step stays in the compact set $\mathcal Y$
-- statement:
--   Suppose Assumption 2 holds ($\mathcal X=\{x:F(x)\le F(x^{(0)})\}$ is compact, $x^{(0)}\in\operatorname{dom}F$), and let $\bar g_{\mathcal X}>0$ bound $g$ on $\mathcal X$ (Remark 1(i)). Let $x\in\mathcal X$, $(x,y)\in\operatorname{dom}Q$ and $\underline\alpha>0$. Then for every $\alpha\ge\underline\alpha$ the point $y^+(\alpha)=\operatorname{prox}_{\alpha g^*}(y+\alpha x)$ lies in
--   $$
--   \mathcal Y=\bigcup_{z\in\mathcal X_{\underline\alpha}}\partial g(z),\qquad \mathcal X_{\underline\alpha}=\{z:\operatorname{dist}^2(z,\mathcal X)\le\bar g_{\mathcal X}/\underline\alpha\},
--   $$
--   and $\mathcal Y$ is compact.
--
--   Together with Lemma 4.3 it confines the $y$-iterates to a compact set.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
--   - encoding: y = prox_{αg*}(·) and x_i(α) ∈ prox_{αf_i}(·) → membership in the argmin set proxSet α φ v; reason: the prox of the convex g* is a single point, so membership and equality agree; the prox of f_i is set-valued as on p.13
--   - reading: ḡ_X > 0 given by Remark 1(i) → any gbar > 0 with g ≤ gbar on X, a parameter of Y and S; reason: Remark 1(i) only asserts that such a bound exists and every result holds for each one; η ≤ g is Fenchel–Young, not a hypothesis
--   - encoding: x^(0) of Assumption 2 (the input of Step 0, x^(0) ∈ dom(F)) → a point x0 with hypothesis F x0 ≠ ⊤; reason: Step 0 of Algorithm 1 requires x^(0) ∈ dom(F), and Assumption 2 refers to that point
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.15, Lemma 4.4 (with Remark 1(i))

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_FracMPGA_proxSet
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1
import Definitions.Def_FracMPGA_setS

namespace FracMPGA

/-- **Lemma 4.4** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.15: suppose that Assumption 2 holds.
Let `x ∈ X`, `(x, y) ∈ dom(Q)`, and `α̲ > 0`. For any `α ∈ [α̲, +∞)`, the vector
`y⁺(α) = prox_{αg*}(y + αx)` falls into the compact set `Y := ⋃_{z ∈ X_α̲} ∂g(z)` with
`X_α̲ := {z ∈ ℝⁿ : dist²(z, X) ≤ ḡ_X/α̲}`, where `ḡ_X > 0` is given by Remark 1(i).

**Formalization Note** Assumption 1 is `hA1`; Assumption 2 is `IsCompact (P.levelX x0)`, with
`x0 = x⁽⁰⁾ ∈ dom(F)` the input of Step 0 of Algorithm 1. `ḡ_X` is any `gbar > 0` with `g ≤ gbar`
on `X` (Remark 1(i); `η ≤ g` there is Fenchel–Young and is not a hypothesis). The conclusion has
both parts: membership for every `α ≥ α̲` and every element of the prox set, and compactness
of `Y`. -/
theorem lemma_4_4 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (x0 : Vec n)
    (hx0 : P.F x0 ≠ ⊤) (hA2 : IsCompact (P.levelX x0)) (gbar : ℝ) (hgbar : 0 < gbar)
    (hgX : ∀ z ∈ P.levelX x0, P.g z ≤ gbar) (x y : Vec n) (hx : x ∈ P.levelX x0)
    (hxy : P.Q x y ≠ ⊤) (αlo : ℝ) (hαlo : 0 < αlo) :
    (∀ α : ℝ, αlo ≤ α →
      ∀ yp ∈ proxSet α (ConvexOptimization.fenchelConjugate P.g) (y + α • x),
        yp ∈ P.setY x0 gbar αlo) ∧
    IsCompact (P.setY x0 gbar αlo) := by sorry

end FracMPGA
