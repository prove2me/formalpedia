-- Prove2me | Theorems.Thm_LonelyRunner_SharedSlowestHalf_strict_of_two_half
-- name    : LonelyRunner.SharedSlowestHalf.strict_of_two_half
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:17.21816+00:00
-- url     : https://prove2.me/theorems/e75317d8-e61e-4274-81fd-b644b098ec67
-- title:
--   Two half-phase blockers of a slower repair leave a strict time
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,m,q,u\in\mathbb N$ with $r\ge7$, $r+2\le n\le2r$, $m>0$, $r\in R$, $n<m(n-r)$, and $mr<q<u$. Assume $r\mid2q$, $r\mid2u$, $r\nmid q$, and $r\nmid u$. Then $S(n,R,\{mr,q,u\})$ has a strict time.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/SharedSlowestHalf.lean, lines 51–111, declaration LonelyRunner.SharedSlowestHalf.strict_of_two_half. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.SharedSlowestHalf
open CollectiveSecondFastest CollectiveUnits BadCover

/-- Two half-phase blockers always leave a strict primitive flank. -/
theorem LonelyRunner.SharedSlowestHalf.strict_of_two_half {n r m q u : ℕ} {R : Finset ℕ}
    (hr : 7 ≤ r) (hrmax : r+2 ≤ n) (hm : 0 < m)
    (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hfull : n < m*(n-r))
    (hpq : m*r < q) (hqu : q < u)
    (hq : r ∣ 2*q) (hu : r ∣ 2*u) (hnq : ¬r ∣ q) (hnu : ¬r ∣ u) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by sorry
