-- Prove2me | Theorems.Thm_GradedReserve_eq_29_certificate
-- name    : GradedReserve.eq_29_certificate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:55.117708+00:00
-- url     : https://prove2.me/theorems/a9691a44-6a90-424d-a98f-fbdeb2d5a0ef
-- title:
--   (29) — the certificate $C[x]-C[x^*]\ge\Lambda(G[x]-G[x^*])$
-- statement:
--   Let $F(v)=v^k$ ($k\ge1$ real), $n\ge2$ and $p>p_{\min}$. For every non-decreasing $x:(0,1)\to[0,1]$,
--   $$C[x]-C[x^*]\ \ge\ \Lambda\big(G[x]-G[x^*]\big).$$
--
--   In particular every $x$ that meets the guarantee, $G[x]\ge\tau-R_0=G[x^*]$, has anchored loss at least $C[x^*]$; this single inequality replaces an infinite-dimensional duality argument.
--
--   **Formalization Note** Only the outer inequality of (29) is stated; its middle lines are the proof.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: functions x on (0,1) (resp. w) → x : ℝ → ℝ, constrained on (0,1); reason: values outside (0,1) are never used
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (29), p.19 (PDF 20); stated as (6), p.7 (PDF 8)

import Mathlib
import Definitions.Def_GradedReserve_Cfun__99e74d
import Definitions.Def_GradedReserve_Gfun__98692e
import Definitions.Def_GradedReserve_lam
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_xStar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Display (29)** (the certificate; stated as (6), p.7) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (29), p.19, PDF 20):
for `p > p_min` and every feasible-domain function `x` (non-decreasing, `0 ≤ x ≤ 1`),
`C[x] − C[x*] ≥ Λ (G[x] − G[x*])`.

**Formalization Note.** Only the outer inequality of (29) is stated; its middle lines are the
proof. `x` is constrained on `(0, 1)` only. -/
theorem eq_29_certificate (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) (p : ℝ)
    (hp : pMin k n < p) (x : ℝ → ℝ) (hx : MonotoneOn x (Ioo 0 1))
    (hx01 : ∀ t ∈ Ioo (0:ℝ) 1, x t ∈ Icc (0:ℝ) 1) :
    lam k n p * (Gfun k n x - Gfun k n (xStar k n p)) ≤
      Cfun k n x - Cfun k n (xStar k n p) := by sorry

end GradedReserve
