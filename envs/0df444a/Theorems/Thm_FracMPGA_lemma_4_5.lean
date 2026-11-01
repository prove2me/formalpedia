-- Prove2me | Theorems.Thm_FracMPGA_lemma_4_5
-- name    : FracMPGA.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:44.869989+00:00
-- url     : https://prove2.me/theorems/f0846701-ae9d-421c-987f-fb6ba6a5608f
-- title:
--   Lemma 4.5 — the $x$-block proximal gradient step for small step sizes
-- statement:
--   Suppose Assumption 2 holds, and let $\mathcal S$ be built from a bound $\bar g_{\mathcal X}$ and $\underline\alpha>0$. For $(x,y)\in\mathcal S$ with $Q(x,y)\le F(x^{(0)})$, a block $i$ and $\alpha>0$, let $x_i^+(\alpha)\in\operatorname{prox}_{\alpha f_i}\big(x_i-\alpha\nabla_ih(x)+\alpha Q(x,y)y_i\big)$ and let $x^{+,i}(\alpha)$ be $x$ with block $i$ replaced by $x_i^+(\alpha)$. Then
--
--   1. for every $\sigma>0$ there is $\underline\alpha_{\mathcal S,\sigma}>0$ such that
--   $$
--   \zeta(x^{+,i}(\alpha))+\tfrac\sigma2\|x^{+,i}(\alpha)-x\|_2^2\le c\,\eta(x^{+,i}(\alpha),y)\tag{23}
--   $$
--   for every $(x,y)\in\mathcal S$ with $Q(x,y)\le F(x^{(0)})$, every $\alpha\in(0,\underline\alpha_{\mathcal S,\sigma})$, every block $i$, every choice of $x_i^+(\alpha)$ and every $c\ge Q(x,y)$;
--   2. if $x^{+,i}(\alpha)$ satisfies (23) for some $c\in[0,F(x^{(0)})]$, then $(x^{+,i}(\alpha),y)\in\mathcal S$.
--
--   It is the step-size bound behind the termination of the line search.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
--   - encoding: y = prox_{αg*}(·) and x_i(α) ∈ prox_{αf_i}(·) → membership in the argmin set proxSet α φ v; reason: the prox of the convex g* is a single point, so membership and equality agree; the prox of f_i is set-valued as on p.13
--   - encoding: Q_(t) = Q(x^(t), y^(t)) (or Q(x, y)) inside the prox argument of Step 2-X → (Q x y).toReal (xStepInput); reason: it is evaluated only on dom(Q) (Theorem 4.6(ii), or (x, y) ∈ S), where the real value is Q(x, y)
--   - reading: ḡ_X > 0 given by Remark 1(i) → any gbar > 0 with g ≤ gbar on X, a parameter of Y and S; reason: Remark 1(i) only asserts that such a bound exists and every result holds for each one; η ≤ g is Fenchel–Young, not a hypothesis
--   - encoding: x^(0) of Assumption 2 (the input of Step 0, x^(0) ∈ dom(F)) → a point x0 with hypothesis F x0 ≠ ⊤; reason: Step 0 of Algorithm 1 requires x^(0) ∈ dom(F), and Assumption 2 refers to that point
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, pp.16–17, Lemma 4.5

import Mathlib
import Definitions.Def_FracMPGA_proxSet
import Definitions.Def_FracMPGA_liftedRatio
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1
import Definitions.Def_FracMPGA_setS
import Definitions.Def_FracMPGA_IsMPGARun

namespace FracMPGA

/-- **Lemma 4.5** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.16: suppose that Assumption 2 holds.
For `(x, y) ∈ S` satisfying `Q(x, y) ≤ F(x⁽⁰⁾)`, let
`x⁺_i(α) ∈ prox_{αf_i}(x_i − α∇_i h(x) + αQ(x, y) y_i)` and
`x^{+,i}(α) = [x_1; …; x_{i−1}; x⁺_i(α); x_{i+1}; …; x_N]`. Then
(i) for any `σ > 0` there exists `α̲_{S,σ} > 0` such that
`ζ(x^{+,i}(α)) + σ/2 ‖x^{+,i}(α) − x‖₂² ≤ c η(x^{+,i}(α), y)` (23)
holds for any `(x, y) ∈ S` with `Q(x, y) ≤ F(x⁽⁰⁾)`, `α ∈ (0, α̲_{S,σ})`, `i ∈ ℕ_N` and
`c ∈ [Q(x, y), +∞)`;
(ii) if `x^{+,i}(α)` satisfies (23) for some `c ∈ [0, F(x⁽⁰⁾)]`, then `(x^{+,i}(α), y) ∈ S`.

**Formalization Note** Assumption 1 is `hA1`; Assumption 2 is `IsCompact (P.levelX x0)` with
`x0 = x⁽⁰⁾ ∈ dom(F)`. `S = P.setS x0 gbar αlo` for a bound `ḡ_X = gbar` of Remark 1(i) and the
lower step size `α̲ = αlo > 0` of Algorithm 1. (23) is `P.lsTest σ c x y x⁺`. In (i) the constant
`α̲_{S,σ}` is uniform over `(x, y)`, `α`, the block `i`, `c` and every element `x⁺_i(α)` of the
(possibly set-valued) prox. In (ii) `σ > 0` and `α > 0` are arbitrary. -/
theorem lemma_4_5 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (x0 : Vec n)
    (hx0 : P.F x0 ≠ ⊤) (hA2 : IsCompact (P.levelX x0)) (gbar : ℝ) (hgbar : 0 < gbar)
    (hgX : ∀ z ∈ P.levelX x0, P.g z ≤ gbar) (αlo : ℝ) (hαlo : 0 < αlo) :
    (∀ σ : ℝ, 0 < σ → ∃ αS : ℝ, 0 < αS ∧
      ∀ x y : Vec n, pair x y ∈ P.setS x0 gbar αlo → P.Q x y ≤ P.F x0 →
        ∀ α : ℝ, 0 < α → α < αS → ∀ r : Fin N,
          ∀ p ∈ proxSet α (P.fb r) (P.xStepInput x y r α),
            ∀ c : ℝ, P.Q x y ≤ (c : EReal) → P.lsTest σ (c : EReal) x y (P.blockUpdate x r p)) ∧
    (∀ σ : ℝ, 0 < σ → ∀ x y : Vec n, pair x y ∈ P.setS x0 gbar αlo → P.Q x y ≤ P.F x0 →
      ∀ α : ℝ, 0 < α → ∀ r : Fin N, ∀ p ∈ proxSet α (P.fb r) (P.xStepInput x y r α),
        ∀ c : ℝ, 0 ≤ c → (c : EReal) ≤ P.F x0 →
          P.lsTest σ (c : EReal) x y (P.blockUpdate x r p) →
            pair (P.blockUpdate x r p) y ∈ P.setS x0 gbar αlo) := by sorry

end FracMPGA
