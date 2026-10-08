-- Prove2me | Theorems.Thm_Helfgott_parity_major_arc_balls_disjoint
-- name    : Helfgott.parity_major_arc_balls_disjoint
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T07:55:55.585996+00:00
-- url     : https://prove2.me/theorems/e1c6f999-7dba-4d23-81a6-904ebc99595f
-- title:
--   Sharp disjointness of parity-dependent rational arcs at the prime large-sieve cutoff
-- statement:
--   Let $\delta,R\ge0$, $x>0$, and $2\delta R^2\le x$. Consider two distinct reduced fractions $a/q$ and $b/d$, represented by $0\le a<q$ and $0\le b<d$, with positive denominators. For an odd denominator require $q\le R$ and give its arc radius $\delta R/(2qx)$; for an even denominator require $q\le2R$ and give its radius $\delta R/(qx)$. Apply the same rules to $d$. Then these two open arcs in $\mathbb R/\mathbb Z$ are disjoint.
--
--   The result includes the boundary case $x=2\delta R^2$. In particular it applies at $R=\sqrt{x/(2\delta)}$, the enlarged denominator cutoff used by Helfgott's prime large sieve. The strengthened separation for pairs of even denominators is retained, allowing exactly the parity-dependent arc family used in the actual three-prime analytic reduction.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, proof of Proposition 5.2 (paragraph after (5.6)); rational-circle separation and parity argument formalized here. Written by Codex.

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_ArcCounting
open Set Metric
open scoped Classical

namespace Helfgott

theorem parity_major_arc_balls_disjoint {a q b d : ℕ} {δ R x : ℝ}
    (hq : 0 < q) (hd : 0 < d) (ha : a < q) (hb : b < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hxpos : 0 < x) (hx : 2*δ*R^2 ≤ x)
    (hqr : (Odd q ∧ (q : ℝ) ≤ R) ∨ (Even q ∧ (q : ℝ) ≤ 2*R))
    (hdr : (Odd d ∧ (d : ℝ) ≤ R) ∨ (Even d ∧ (d : ℝ) ≤ 2*R))
    (hne : (a,q) ≠ (b,d)) :
    Disjoint
      (ball ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))
        (if Odd q then δ*R/(2*q*x) else δ*R/(q*x)))
      (ball ((b : ℝ)/(d : ℝ) : AddCircle (1 : ℝ))
        (if Odd d then δ*R/(2*d*x) else δ*R/(d*x))) := by sorry

end Helfgott
