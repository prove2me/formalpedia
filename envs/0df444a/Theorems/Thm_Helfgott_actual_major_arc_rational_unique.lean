-- Prove2me | Theorems.Thm_Helfgott_actual_major_arc_rational_unique
-- name    : Helfgott.actual_major_arc_rational_unique
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T04:32:48.102652+00:00
-- url     : https://prove2.me/theorems/dafde76e-a6dc-469f-b3ef-b098afbe9ac1
-- title:
--   Disjointness and unique rational centers for the actual odd/even Goldbach major arcs
-- statement:
--   Let $r$ be a natural cutoff and $x$ a real scale satisfying $x>32r^2$. For a point $\alpha$ on the unit additive circle, suppose two reduced fractions $a/q$ and $b/d$, with positive denominators and $0\le a<q$, $0\le b<d$, satisfy the Goldbach major-arc conditions. Odd denominators are at most $r$ with radius $4r/(qx)$; even denominators are at most $2r$ with radius $8r/(qx)$. Then
--
--   $$a=b\qquad\text{and}\qquad q=d.$$
--
--   Thus the actual odd/even rational major arcs are pairwise disjoint. At $r=150000$, the sufficient scale condition is $x>720000000000$, which is far below the analytic range $x\ge49\cdot10^{25}$. This permits the major-arc integral to be decomposed into individual reduced-rational contributions without double-counting.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, the major-arc definition in §3 and the cutoffs in §7.2. The explicit sufficient separation condition is independently derived. Written by Codex.

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.Nat.GCD.Basic
open Set Metric

namespace Helfgott

theorem actual_major_arc_rational_unique {a q b d r : ℕ} {x : ℝ}
    (α : AddCircle (1:ℝ)) (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hx : 32*(r:ℝ)^2 < x)
    (hαq : (Odd q ∧ q ≤ r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*q*x)) ∨
      (Even q ∧ q ≤ 2*r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) < 8*r/(q*x)))
    (hαd : (Odd d ∧ d ≤ r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*d*x)) ∨
      (Even d ∧ d ≤ 2*r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) < 8*r/(d*x))) :
    a = b ∧ q = d := by sorry

end Helfgott
