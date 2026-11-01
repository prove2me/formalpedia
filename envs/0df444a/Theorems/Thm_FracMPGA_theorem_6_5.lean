-- Prove2me | Theorems.Thm_FracMPGA_theorem_6_5
-- name    : FracMPGA.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:43:13.523845+00:00
-- url     : https://prove2.me/theorems/386493e4-c33a-4c31-8a8b-8197623387f8
-- title:
--   Theorem 6.5 — under the KL property, the iterates of CMPGA$_{\rm ML}$ converge to a critical point of $F$
-- statement:
--   Consider problem (1) under its standing assumptions, and run CMPGA$_{\rm ML}$ (Algorithm 1 with cyclic block order and the monotone line search, $M=0$) with any parameters $0<\underline\alpha\le\bar\alpha$, $\sigma>0$, $0<\gamma<1$, from any $x^{(0)}\in\operatorname{dom}F$ and $y^{(0)}\in\partial g(x^{(0)})$. Suppose that
--
--   1. (Assumption 2) the level set $\mathcal X=\{x:F(x)\le F(x^{(0)})\}$ is compact;
--   2. (Assumption 3) $f$ is locally Lipschitz continuous on $\mathcal X$;
--   3. (Assumption 4) $g^*$ satisfies the calmness condition on $\operatorname{dom}g^*$;
--   4. $Q$ satisfies the KL property at every point of $\mathcal S$.
--
--   Then the whole sequence $(x^{(t)})_{t\in\mathbb N}$ converges,
--   $$
--   \lim_{t\to\infty}x^{(t)}=x^\star,
--   $$
--   and $x^\star\in\operatorname{dom}F$ is a critical point of $F$: $0\in\hat\partial f(x^\star)+\nabla h(x^\star)-F(x^\star)\partial g(x^\star)$.
--
--   This is the paper's main convergence guarantee for its algorithm on nonsmooth, nonconvex single-ratio fractional programs, including the $L_1/L_2$ and $L_1/S_K$ sparse-recovery models.
--
--   **Formalization Note** In hypothesis 4, $\mathcal S$ is built from some bound $\bar g_{\mathcal X}>0$ of $g$ on $\mathcal X$ (Remark 1(i)), and the KL property is required at the points of $\mathcal S$ where the limiting subdifferential of $Q$ is nonempty, Definition 1 being posed at points of $\operatorname{dom}\partial\varphi$.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
--   - encoding: y = prox_{αg*}(·) and x_i(α) ∈ prox_{αf_i}(·) → membership in the argmin set proxSet α φ v; reason: the prox of the convex g* is a single point, so membership and equality agree; the prox of f_i is set-valued as on p.13
--   - encoding: Q_(t) = Q(x^(t), y^(t)) (or Q(x, y)) inside the prox argument of Step 2-X → (Q x y).toReal (xStepInput); reason: it is evaluated only on dom(Q) (Theorem 4.6(ii), or (x, y) ∈ S), where the real value is Q(x, y)
--   - encoding: Step 2-X: backtrack α ← αγ from α̃(t) until the test holds → trial points p k at α̃(t)γᵏ for k ≤ j, the test failing for k < j and holding at k = j; α(t) = α̃(t)γʲ; reason: the same runs; the failed trials are recorded because Theorem 4.6(i) is about them
--   - encoding: Q_(l(t)) with l(t) = max{j ≤ t : Q_(j) = max{Q_(s) : [t − M]₊ ≤ s ≤ t}} → Qwin M x y t = ⨆ s ∈ [t − M, t], Q(x s, y s) in EReal (ℕ subtraction is [·]₊); reason: Q_(l(t)) is that maximum; the index l(t) is not needed
--   - generalization: one y-step size α := α̃_Y ∈ [α̲, ᾱ] in Algorithm 1 → a y-step size α(t) ∈ [α̲, ᾱ] that may differ between y-steps; reason: §5.1 (39) writes 'some α(k,0) ∈ [α̲, ᾱ]' and the proofs use only α(t) ∈ [α̲, ᾱ]; a constant α̃_Y is the special case, so the statement specializes to the source
--   - reading: Assumption 3: f is locally Lipschitz continuous on X → Assumption3: every point of X has a neighbourhood U and L with f u ≤ f v + L‖u − v‖ for u, v ∈ U ∩ X; reason: relative to X; the paper says Assumption 3 holds automatically for its models (2), (3) (p.29), whose f is +∞ just outside a box, so Lipschitz continuity on full neighbourhoods would exclude them
--   - encoding: calmness |φ(u) − φ(x)| ≤ κ‖u − x‖₂ (p.6) → the two inequalities φ u ≤ φ x + κ‖u − x‖ and φ x ≤ φ u + κ‖u − x‖ in EReal; reason: with φ(x) finite they say the same
--   - reading: 'If Q satisfies the KL property at any (x, y) ∈ S' with S built from ḡ_X of Remark 1(i) → ∃ gbar > 0 with g ≤ gbar on X such that Q has the KL property at every p ∈ S(gbar) with ∂Q(p) ≠ ∅; reason: Definition 1 (p.8) defines the KL property only at points of dom(∂φ); ḡ_X is only asserted to exist, and the smallest admissible S gives the weakest hypothesis
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §6.1, p.28, Theorem 6.5 (proof pp.28–29)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracMPGA_liftedRatio
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1
import Definitions.Def_FracMPGA_IsCritical
import Definitions.Def_FracMPGA_setS
import Definitions.Def_FracMPGA_Assumption3
import Definitions.Def_FracMPGA_Assumption4
import Definitions.Def_FracMPGA_IsMPGARun
open Filter Topology NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracMPGA

/-- **Theorem 6.5** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.28: suppose that Assumptions 2–4
hold. If `Q` satisfies the KL property at any `(x, y) ∈ S`, then the sequence `{x⁽ᵗ⁾ : t ∈ ℕ}`
generated by CMPGA_ML converges to a critical point `x⋆` of `F`.

**Formalization Note** Assumption 1 (blanket) is `hA1`; Assumption 2 is
`IsCompact (P.levelX (x 0))`, Assumption 3 is `Assumption3 P (x 0)`, Assumption 4 is
`Assumption4 P`. `(x, y, α)` is any run of CMPGA_ML (Algorithm 1, cyclic, `M = 0`) for any
parameters with `0 < α̲ ≤ ᾱ`, `σ > 0`, `0 < γ < 1` and any start `x⁽⁰⁾ ∈ dom(F)`,
`y⁽⁰⁾ ∈ ∂g(x⁽⁰⁾)` (part of `IsCMPGAMLRun`). The KL hypothesis reads: for some bound `ḡ_X > 0` of
`g` on `X` (Remark 1(i)), `Q` has the KL property (Definition 1, `HasKLProperty` of `Q` on the
Euclidean product) at every point of `S` (built from that `ḡ_X`) at which the limiting
subdifferential of `Q` is nonempty, i.e. at every point of `S ∩ dom(∂Q)`, Definition 1 being
posed at points of `dom(∂φ)`. The conclusion concerns the whole sequence `x⁽ᵗ⁾`, and
`IsCritical` includes `x⋆ ∈ dom(F)`. -/
theorem theorem_6_5 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (αlo αhi σ γ : ℝ)
    (x y : ℕ → Vec n) (α : ℕ → ℝ) (hrun : P.IsCMPGAMLRun αlo αhi σ γ x y α)
    (hA2 : IsCompact (P.levelX (x 0))) (hA3 : Assumption3 P (x 0)) (hA4 : Assumption4 P)
    (hKL : ∃ gbar : ℝ, 0 < gbar ∧ (∀ z ∈ P.levelX (x 0), P.g z ≤ gbar) ∧
      ∀ p ∈ P.setS (x 0) gbar αlo, (LimitingSubdiff P.Qp p).Nonempty → HasKLProperty P.Qp p) :
    ∃ xstar : Vec n, Tendsto x atTop (𝓝 xstar) ∧ IsCritical P xstar := by sorry

end FracMPGA
