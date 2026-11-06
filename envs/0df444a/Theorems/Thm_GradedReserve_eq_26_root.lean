-- Prove2me | Theorems.Thm_GradedReserve_eq_26_root
-- name    : GradedReserve.eq_26_root
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:32.198111+00:00
-- url     : https://prove2.me/theorems/380ae002-b2f7-4d0f-8284-2602f98ab73e
-- title:
--   (26) — the candidate, $0<\bar v<r^*$, and the unique root of (3)
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real) and $n\ge2$. For $p>p_{\min}=(\sqrt{\ell^2+4km}-\ell)/2$ (26):
--
--   1. $0<\bar v<r^*$;
--   2. the candidate $x^*(t)=\bar v^{\,\ell}t^{\ell/p}$ has $\widetilde M^*(t)=\frac p{p+\ell}x^*(t)$ and level bid $B^*(t)=c_0\bar v\,t^{1/p}$ for $t\in(0,1)$;
--   3. its rational revenue $R_0+G[x^*]$ is the left side of (3).
--
--   Moreover the left side of (3) is strictly increasing in $p$ on $(p_{\min},\infty)$, tends to $R_n(0)=R_0$ as $p\downarrow p_{\min}$ and to $R^*$ as $p\to\infty$; hence for every $R_0<\tau<R^*$ equation (3) has a unique root $p>p_{\min}$.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: R_n(r) = n ∫_r^1 φ Q f → n ∫_r^1 (v f(v) − (1 − F(v))) Q(v) dv; reason: equal wherever f > 0, i.e. almost everywhere; avoids x/0 = 0
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (26), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_Gfun__98692e
import Definitions.Def_GradedReserve_bidX
import Definitions.Def_GradedReserve_cZero
import Definitions.Def_GradedReserve_hardyAvg
import Definitions.Def_GradedReserve_lhs3
import Definitions.Def_GradedReserve_optRevenue
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_rStar
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_xStar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Display (26) and the root of (3)** (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19): for `p > p_min`,
`0 < v̄ < r*`; the candidate `x*(t) = v̄^ℓ t^{ℓ/p}` has `M̃*(t) = p/(p+ℓ) x*(t)` and
`B*(t) = c₀ v̄ t^{1/p}`; its rational revenue `R₀ + G[x*]` is the left side of (3); this
expression is strictly increasing in `p`, tends to `R_n(0)` as `p ↓ p_min` and to `R*` as
`p → ∞`; hence (3) has a unique root `p > p_min` for every `R₀ < τ < R*`.

**Formalization Note.** `R₀ = R_n(0)` and `R*` are the defined revenue curve (1) of the power law
at `0` and at `r*`. -/
theorem eq_26_root (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    (∀ p, pMin k n < p → 0 < vbar k n p ∧ vbar k n p < rStar (powerDensity k)) ∧
    (∀ p, pMin k n < p → ∀ t ∈ Ioo (0:ℝ) 1,
      hardyAvg (xStar k n p) t = p / (p + powL k n) * xStar k n p t ∧
      bidX k n (xStar k n p t) (hardyAvg (xStar k n p) t) =
        cZero k n p * vbar k n p * t ^ (1 / p)) ∧
    (∀ p, pMin k n < p →
      revCurve (powerDensity k) n 0 + Gfun k n (xStar k n p) = lhs3 k n p) ∧
    StrictMonoOn (lhs3 k n) (Ioi (pMin k n)) ∧
    Tendsto (lhs3 k n) (𝓝[>] (pMin k n)) (𝓝 (revCurve (powerDensity k) n 0)) ∧
    Tendsto (lhs3 k n) atTop (𝓝 (optRevenue (powerDensity k) n)) ∧
    (∀ τ, revCurve (powerDensity k) n 0 < τ → τ < optRevenue (powerDensity k) n →
      ∃! p, pMin k n < p ∧ lhs3 k n p = τ) := by sorry

end GradedReserve
