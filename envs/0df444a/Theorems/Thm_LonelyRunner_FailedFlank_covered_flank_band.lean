-- Prove2me | Theorems.Thm_LonelyRunner_FailedFlank_covered_flank_band
-- name    : LonelyRunner.FailedFlank.covered_flank_band
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:26.151346+00:00
-- url     : https://prove2.me/theorems/35aad0f2-27b5-4507-a5bf-9754dc6a853b
-- title:
--   A failed primitive flank lies in one band of the second insertion
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,m,b,q\in\mathbb N$ and $a,c\in\mathbb Z$. Assume $n\ge5$, $n\le2r$, $r<n$, $2\le m$, $m+1\le n$, $q>0$, $n-r\le b<m(n-r)$, and $ab-cr=1$. Suppose $S(n,\{r,s\},\{mr,q\})$ has no strict time. Put $\alpha=a/r-1/(nmr)$ and $\beta=a/r-(n-r)/(nrb)$. Then
--
--   $$\exists j\in\mathbb Z:\quad |q\alpha-j|\le1/n\quad\text{and}\quad |q\beta-j|\le1/n.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/FailedFlank.lean, lines 129–218, declaration LonelyRunner.FailedFlank.covered_flank_band. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.FailedFlank
open Farey BadCover LargeDeletionMatching

set_option maxHeartbeats 1200000 in

theorem LonelyRunner.FailedFlank.covered_flank_band {n r s m b q : ℕ} {a c : ℤ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hmn : m+1 ≤ n) (hq : 0 < q)
    (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hunit : a*(b:ℤ)-c*(r:ℤ)=1)
    (hno : ¬ HasStrictTime n r s (m*r) q) :
    ∃ j : ℤ,
      |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n ∧
      |(q:ℝ)*((a:ℝ)/r-((n:ℝ)-r)/((n:ℝ)*r*b))-j| ≤ 1/n := by sorry
