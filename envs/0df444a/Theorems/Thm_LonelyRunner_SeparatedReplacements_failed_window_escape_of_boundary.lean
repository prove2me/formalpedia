-- Prove2me | Theorems.Thm_LonelyRunner_SeparatedReplacements_failed_window_escape_of_boundary
-- name    : LonelyRunner.SeparatedReplacements.failed_window_escape_of_boundary
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:28.329018+00:00
-- url     : https://prove2.me/theorems/34a4f22e-fd8b-4738-87c7-3cdfc54fd9ad
-- title:
--   A safe second insertion at every failed boundary gives a strict time
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,m,z,b\in\mathbb N$ satisfy $n\ge5$, $n\le2r$, $r<n$, $m\ge2$, $n-r\le b<m(n-r)$, and $\gcd(r,b)=1$. Suppose for every $a,c\in\mathbb Z$ with $ab-cr=1$ one has $d(z(a/r-1/(nmr)))>1/n$. Then
--
--   $$S(n,\{r,s\},\{mr,z\})\text{ has a strict time}.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/SeparatedReplacements.lean, lines 24–79, declaration LonelyRunner.SeparatedReplacements.failed_window_escape_of_boundary. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.SeparatedReplacements
open LargeDeletionMatching SeparatedBands

set_option maxHeartbeats 1000000 in

theorem LonelyRunner.SeparatedReplacements.failed_window_escape_of_boundary {n r s m z b : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n) (hm : 2 ≤ m)
    (hab : n-r ≤ b) (hfail : b < m*(n-r)) (hcop : Nat.Coprime r b)
    (hsafe : ∀ a c : ℤ, a*(b:ℤ)-c*(r:ℤ)=1 →
      (1:ℝ)/n < ndist ((z:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)))) :
    HasStrictTime n r s (m*r) z := by sorry
