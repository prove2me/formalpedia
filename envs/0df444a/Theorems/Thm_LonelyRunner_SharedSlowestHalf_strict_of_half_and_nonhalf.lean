-- Prove2me | Theorems.Thm_LonelyRunner_SharedSlowestHalf_strict_of_half_and_nonhalf
-- name    : LonelyRunner.SharedSlowestHalf.strict_of_half_and_nonhalf
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:23.853507+00:00
-- url     : https://prove2.me/theorems/88d654a4-7120-4661-9304-dc37343a1ccc
-- title:
--   One active half-phase blocker and one non-half-phase blocker escape
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,m,Q,w\in\mathbb N$ with $r\ge7$, $r+2\le n\le2r$, $m>0$, $r\in R$, $n<m(n-r)$, and $mr<Q$. Assume $r\mid2Q$, $r\nmid Q$, $r\nmid2w$, and $d(1/2-Q/(nmr))\le1/n$. Then $S(n,R,\{mr,Q,w\})$ has a strict time. No upper bound or ordering is imposed on $w$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/SharedSlowestHalf.lean, lines 113–197, declaration LonelyRunner.SharedSlowestHalf.strict_of_half_and_nonhalf. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.SharedSlowestHalf
open CollectiveSecondFastest CollectiveUnits BadCover

/-- An active half-phase blocker and any non-half-phase blocker leave a strict
time; the latter's speed may be arbitrarily large. -/
theorem LonelyRunner.SharedSlowestHalf.strict_of_half_and_nonhalf {n r m Q w : ℕ} {R : Finset ℕ}
    (hr : 7 ≤ r) (hrmax : r+2 ≤ n) (hm : 0 < m)
    (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hfull : n < m*(n-r))
    (hpQ : m*r < Q) (hd : r ∣ 2*Q) (hnQ : ¬r ∣ Q)
    (hnw : ¬r ∣ 2*w)
    (hband : ndist (1/2-((Q:ℝ)/((m:ℝ)*r))/(n:ℝ)) ≤ 1/(n:ℝ)) :
    SeparatedMulti.HasStrictTime n R {m*r,Q,w} := by sorry
