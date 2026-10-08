-- Prove2me | Theorems.Thm_LonelyRunner_FastestBoundary_boundary_blocker
-- name    : LonelyRunner.FastestBoundary.boundary_blocker
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:03:18.795971+00:00
-- url     : https://prove2.me/theorems/1ef0a39e-77be-495f-80c0-38235946edb8
-- title:
--   Failure of strictness forces an inserted boundary blocker
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,m,b\in\mathbb N$ and $a,c\in\mathbb Z$. Assume $n\ge5$, $r\in R$, $r<n\le2r$, $m\ge2$, $n-r\le b<m(n-r)$, and $ab-cr=1$. If no strict time exists for $S(n,R,W)$, then some $q\in W\setminus\{mr\}$ satisfies $d(q(a/r-1/(nmr)))\le1/n$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/FastestBoundary.lean, lines 134–184, declaration LonelyRunner.FastestBoundary.boundary_blocker. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.FastestBoundary

/-- If no strict time exists, some other insertion blocks every failed boundary.
There is no separation or cardinality hypothesis. -/
theorem LonelyRunner.FastestBoundary.boundary_blocker {n r m b : ℕ} {a c : ℤ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    ∃ q ∈ W.erase (m*r),
      ndist ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) ≤ 1/n := by sorry
