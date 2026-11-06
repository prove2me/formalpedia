-- Prove2me | Theorems.Thm_GradedReserve_eq_23_25
-- name    : GradedReserve.eq_23_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:31.789198+00:00
-- url     : https://prove2.me/theorems/73dc2e54-1e1b-46a7-b9b6-ae3cd15edfe3
-- title:
--   (23)–(25) — level bid, rational and anchored revenue in $x=w^\ell$
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real), $n\ge2$, and let $w:(0,1)\to[0,1]$ be non-decreasing. Put $x(t)=w(t)^\ell$ and $\widetilde M(t)=t^{-1}\int_0^tx(u)\,du$. Then $\widetilde M=\ell M$, with $M$ as in Lemma 3.2, and for $t\in(0,1)$ the level bid (4) is
--   $$B(t)=B\big(x(t),\widetilde M(t)\big)=\frac{m\,x(t)+\widetilde M(t)}{\ell\,x(t)^{m/\ell}}\qquad(23);$$
--   moreover
--   $$\int_0^1R_n(w(t))\,dt=R_0+G[x]\qquad(24),\qquad \mathbb E[V_{(1)}]-\int_0^1D(B(t))\,dt=\frac N{N+1}-C[x]\qquad(25).$$
--
--   By Lemma 3.2 the two left sides are the rational and the anchored revenue of the canonical mechanism with levels $w$, so the design problem becomes a convex program in $x$.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: R_n(r) = n ∫_r^1 φ Q f → n ∫_r^1 (v f(v) − (1 − F(v))) Q(v) dv; reason: equal wherever f > 0, i.e. almost everywhere; avoids x/0 = 0
--   - encoding: functions x on (0,1) (resp. w) → x : ℝ → ℝ, constrained on (0,1); reason: values outside (0,1) are never used
--   - encoding: measurable non-decreasing w : (0,1) → [0,1] → MonotoneOn w (0,1) with values in [0,1] there; reason: a monotone function on an interval is measurable; the same functions
--   - encoding: Rev_rat = R₀ + G[x], Rev_anc = N/(N+1) − C[x] → ∫₀¹ R_n(w(t)) dt = R₀ + G[x] and E[V₍₁₎] − ∫₀¹ D(B(t)) dt = N/(N+1) − C[x]; reason: Rev_rat and Rev_anc are these expressions by Lemma 3.2
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, displays (23)–(25), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_Cfun__99e74d
import Definitions.Def_GradedReserve_Gfun__98692e
import Definitions.Def_GradedReserve_avgH
import Definitions.Def_GradedReserve_bidX
import Definitions.Def_GradedReserve_expMax
import Definitions.Def_GradedReserve_hardyAvg
import Definitions.Def_GradedReserve_levelBid
import Definitions.Def_GradedReserve_lossD
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_revCurve
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Displays (23)–(25)** (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19): for `F(v) = v^k` and every
non-decreasing `w : (0, 1) → [0, 1]`, with `x(t) = w(t)^ℓ` and its average
`M̃(t) = t⁻¹ ∫₀^t x = ℓ M(t)`, the level bid of Lemma 3.2 is `B = (m x + M̃)/(ℓ x^{m/ℓ})` (23), the
rational revenue `∫₀¹ R_n(w(t)) dt` equals `R₀ + G[x]` (24), and the anchored revenue
`E[V₍₁₎] − ∫₀¹ D(B(t)) dt` equals `N/(N+1) − C[x]` (25).

**Formalization Note.** `w` is any function non-decreasing on `(0, 1)` with values in `[0, 1]`
there (hence measurable); `Rev_rat` and `Rev_anc` of (24)–(25) are the expressions Lemma 3.2 gives
them. -/
theorem eq_23_25 (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (w : ℝ → ℝ)
    (hw : MonotoneOn w (Ioo 0 1)) (hw01 : ∀ t ∈ Ioo (0:ℝ) 1, w t ∈ Icc (0:ℝ) 1) :
    (∀ t ∈ Ioo (0:ℝ) 1,
      hardyAvg (fun u => w u ^ powL k n) t = powL k n * avgH (powerDensity k) n w t ∧
      levelBid (powerDensity k) n w t =
        bidX k n (w t ^ powL k n) (hardyAvg (fun u => w u ^ powL k n) t)) ∧
    ∫ t in (0:ℝ)..1, revCurve (powerDensity k) n (w t) =
      revCurve (powerDensity k) n 0 + Gfun k n (fun u => w u ^ powL k n) ∧
    expMax (powerDensity k) n
        - ∫ t in (0:ℝ)..1, lossD (powerDensity k) n (levelBid (powerDensity k) n w t) =
      powN k n / (powN k n + 1) - Cfun k n (fun u => w u ^ powL k n) := by sorry

end GradedReserve
