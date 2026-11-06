-- Prove2me | Theorems.Thm_GradedReserve_eq_27_28_adjoint
-- name    : GradedReserve.eq_27_28_adjoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:46.548865+00:00
-- url     : https://prove2.me/theorems/61b16456-6a93-4ab7-9325-8ababa48674f
-- title:
--   (27)–(28) — the adjoint identity at the candidate, $\Lambda=c_0^N\bar v^kp>0$
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real), $n\ge2$ and $p>p_{\min}$. Then $\Lambda=c_0^N\bar v^{\,k}p>0$ (28), and for every $t\in(0,1)$, at the candidate $\big(x^*(t),\widetilde M^*(t)\big)$ with $\widetilde M^*=\frac p{p+\ell}x^*$, the partial derivatives of $c$ are
--   $$c_x(t)=\frac N\ell c_0^N\bar v^{\,k}\frac m{p+\ell}t^{k/p},\qquad c_{\widetilde M}(t)=\frac N\ell c_0^N\bar v^{\,k}t^{k/p},$$
--   and they satisfy the adjoint identity
--   $$c_x(t)+\int_t^1\frac{c_{\widetilde M}(u)}u\,du=\Lambda\,g'(x^*(t))\qquad(27).$$
--
--   The identity is the first-order condition of the convex program (5) at the candidate, with multiplier $\Lambda$.
--
--   **Formalization Note** The partial derivatives are stated as derivatives of the two sections of $c$ at the candidate.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: the partial derivatives c_x(t), c_M̃(t) at the candidate → HasDerivAt of the sections y ↦ c(y, M̃*(t)) at x*(t) and z ↦ c(x*(t), z) at M̃*(t), with the printed values; reason: the same derivatives (x*(t) > 0, so c is smooth there)
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, displays (27)–(28), p.19 (PDF 20)

import Mathlib
import Definitions.Def_GradedReserve_cMStar
import Definitions.Def_GradedReserve_cfun
import Definitions.Def_GradedReserve_cxStar
import Definitions.Def_GradedReserve_gDeriv
import Definitions.Def_GradedReserve_lam
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_xStar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Displays (27)–(28)** (adjoint identity) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.19, PDF 20): for `p > p_min`,
`Λ = c₀^N v̄^k p > 0`, and at the candidate `(x*(t), M̃*(t))`, `M̃* = p/(p+ℓ) x*`, the partial
derivatives of `c` are `c_x(t) = (N/ℓ) c₀^N v̄^k (m/(p+ℓ)) t^{k/p}` and
`c_M̃(t) = (N/ℓ) c₀^N v̄^k t^{k/p}`, and for every `t ∈ (0, 1)`
`c_x(t) + ∫_t^1 c_M̃(u)/u du = Λ g′(x*(t))`.

**Formalization Note.** The partial derivatives are stated as `HasDerivAt` of the two sections of
`c` at the candidate, with the explicit values printed on p.19. -/
theorem eq_27_28_adjoint (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (p : ℝ)
    (hp : pMin k n < p) :
    0 < lam k n p ∧
    ∀ t ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun y => cfun k n y (p / (p + powL k n) * xStar k n p t)) (cxStar k n p t)
        (xStar k n p t) ∧
      HasDerivAt (fun z => cfun k n (xStar k n p t) z) (cMStar k n p t)
        (p / (p + powL k n) * xStar k n p t) ∧
      cxStar k n p t + ∫ u in t..1, cMStar k n p u / u =
        lam k n p * gDeriv k n (xStar k n p t) := by sorry

end GradedReserve
