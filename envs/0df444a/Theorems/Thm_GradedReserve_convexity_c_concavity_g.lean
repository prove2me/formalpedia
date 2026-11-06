-- Prove2me | Theorems.Thm_GradedReserve_convexity_c_concavity_g
-- name    : GradedReserve.convexity_c_concavity_g
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:22.606006+00:00
-- url     : https://prove2.me/theorems/b129a75d-c51b-492c-8748-a42a4a1ecf37
-- title:
--   Section A.5 — $c$ jointly convex on the wedge, $C$ convex, $g$ concave
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real) and $n\ge2$. Then
--
--   1. $c(x,\widetilde M)=\frac N{N+1}B(x,\widetilde M)^{N+1}$ is jointly convex on the feasible wedge $\{0\le\widetilde M\le x\}$, and continuous there, including at the extension $c(0,0)=0$;
--   2. the non-decreasing functions $0\le x\le1$ on $(0,1)$ form a convex set, on which the anchored loss $C[x]=\int_0^1c(x(t),\widetilde M(t))\,dt$ is convex;
--   3. for $x>0$,
--   $$g'(x)=\frac n\ell\big(1-(k+1)x^{k/\ell}\big),\qquad g''(x)=-\frac{nk(k+1)}{\ell^2}x^{k/\ell-1}<0,$$
--   so $g$ is (strictly) concave.
--
--   Convexity of $C$ and concavity of $G[x]=\int_0^1g(x)$ are what make the first-order certificate (29) global.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: functions x on (0,1) (resp. w) → x : ℝ → ℝ, constrained on (0,1); reason: values outside (0,1) are never used
--   - generalization: g concave (g″ < 0 for x > 0), used on 0 ≤ x ≤ 1 → g strictly concave on [0, ∞); reason: g″ < 0 at every x > 0 as printed; restricting to [0,1] and dropping strictness gives the source's claim
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_Cfun__99e74d
import Definitions.Def_GradedReserve_cfun
import Definitions.Def_GradedReserve_gDeriv
import Definitions.Def_GradedReserve_gDeriv2
import Definitions.Def_GradedReserve_gfun
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Convexity of `c` and `C`, concavity of `g`** (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19): `c` is jointly
convex on the feasible wedge `0 ≤ M̃ ≤ x` and continuous there (including the extension
`c(0, 0) = 0`); the non-decreasing functions `0 ≤ x ≤ 1` form a convex set on which `C` is convex;
`g′(x) = (n/ℓ)(1 − (k+1) x^{k/ℓ})`, `g″(x) = −(nk(k+1)/ℓ²) x^{k/ℓ−1} < 0`, so `g` is concave.

**Formalization Note.** Functions `x` are `ℝ → ℝ`, constrained on `(0, 1)` only. The derivative
formulas are stated for `x > 0`; concavity of `g` is stated as strict concavity on `[0, ∞)`. -/
theorem convexity_c_concavity_g (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    ConvexOn ℝ {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1} (fun q => cfun k n q.1 q.2) ∧
    ContinuousOn (fun q : ℝ × ℝ => cfun k n q.1 q.2) {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1} ∧
    ConvexOn ℝ {x : ℝ → ℝ | MonotoneOn x (Ioo 0 1) ∧ ∀ t ∈ Ioo (0:ℝ) 1, x t ∈ Icc (0:ℝ) 1}
      (Cfun k n) ∧
    (∀ x : ℝ, 0 < x → HasDerivAt (gfun k n) (gDeriv k n x) x ∧
      HasDerivAt (gDeriv k n) (gDeriv2 k n x) x ∧ gDeriv2 k n x < 0) ∧
    StrictConcaveOn ℝ (Ici 0) (gfun k n) := by sorry

end GradedReserve
