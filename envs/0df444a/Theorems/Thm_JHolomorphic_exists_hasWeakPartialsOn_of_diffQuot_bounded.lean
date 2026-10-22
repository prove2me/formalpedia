-- Prove2me | Theorems.Thm_JHolomorphic_exists_hasWeakPartialsOn_of_diffQuot_bounded
-- name    : JHolomorphic.exists_hasWeakPartialsOn_of_diffQuot_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T15:56:16.912026+00:00
-- url     : https://prove2.me/theorems/5692a44b-ac73-41c5-a452-06f66135ea9a
-- title:
--   Uniformly $L^p$-bounded difference quotients give weak partial derivatives in $L^p$ on a disc
-- statement:
--   Let $1<p<\infty$, let $E$ be a finite-dimensional real normed space, let $c\in\mathbb{C}$ and $r<R$, and let $f\in L^p(B(c,R);E)$. Suppose there are $\delta>0$ and $C$ such that for $v=1$ and for $v=i$, and for every real $h$ with $0<|h|<\delta$,
--   $$\Bigl\|\frac{f(\cdot+hv)-f}{h}\Bigr\|_{L^p(B(c,r))}\le C.$$
--   Then $f$ has weak partial derivatives $f_s,f_t$ on $B(c,r)$, and $f_s,f_t\in L^p(B(c,r))$.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn` on the open disc `ball c r`, tested against real $C^\infty$ functions with compact support in it; $f_s$ is the derivative in the direction $1$ and $f_t$ in the direction $i$. The difference quotient is `fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)`. $L^p$ norms and membership use `ENNReal.ofReal p` and the Lebesgue measure restricted to the disc; the bound is `ENNReal.ofReal C`.
-- source:
--   L. C. Evans, Partial Differential Equations, §5.8.2, Theorem 3 (ii); D. Gilbarg, N. Trudinger, Elliptic PDE of Second Order, Lemma 7.24

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `1 < p < ∞`, `r < R`, and let `f ∈ L^p(B(c, R); E)`. If for `v = 1` and `v = i` the difference
quotients `h⁻¹ (f(· + h v) - f)` are bounded in `L^p(B(c, r))` uniformly in real `h` with
`0 < |h| < δ`, then `f` has weak partial derivatives on `B(c, r)`, and both lie in `L^p(B(c, r))`. -/
theorem exists_hasWeakPartialsOn_of_diffQuot_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) {c : ℂ} {r R : ℝ}
    (hrR : r < R) {f : ℂ → E} (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (ball c R)))
    (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hC : ∀ v ∈ ({1, Complex.I} : Set ℂ), ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) (ENNReal.ofReal p)
        (volume.restrict (ball c r)) ≤ ENNReal.ofReal C) :
    ∃ fs ft : ℂ → E, HasWeakPartialsOn (ball c r) f fs ft ∧
      MemLp fs (ENNReal.ofReal p) (volume.restrict (ball c r)) ∧
      MemLp ft (ENNReal.ofReal p) (volume.restrict (ball c r)) := by
  sorry

end JHolomorphic
