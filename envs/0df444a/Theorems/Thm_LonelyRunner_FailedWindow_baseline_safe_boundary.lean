-- Prove2me | Theorems.Thm_LonelyRunner_FailedWindow_baseline_safe_boundary
-- name    : LonelyRunner.FailedWindow.baseline_safe_boundary
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:02:46.858175+00:00
-- url     : https://prove2.me/theorems/9d8fb1dc-77f4-46ac-8539-b1e144ab99f1
-- title:
--   Retained baseline speeds are strict at a failed-window boundary
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $n,r,m,b,a,c,v\in\mathbb Z$ satisfy $0<r<n\le2r$, $m\ge1$, $n-r\le b<m(n-r)$, $ab-cr=1$, and $0<v<n$ with $v\ne r$. Then $d(v(a/r-1/(nmr)))>1/n$. All quotients in the conclusion are real.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/FailedWindow.lean, lines 11–85, declaration LonelyRunner.FailedWindow.baseline_safe_boundary. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.FailedWindow
open Farey BadCover

set_option maxHeartbeats 1000000 in
/-- If b is a unit modulo r in the failed GW window, the left endpoint of
an mr-band is strictly safe for every retained baseline speed. -/
theorem LonelyRunner.FailedWindow.baseline_safe_boundary {n r m b a c v : ℤ}
    (hr : 0 < r) (hrn : r < n) (hlarge : n ≤ 2*r) (hm : 1 ≤ m)
    (hab : n-r ≤ b) (hfail : b < m*(n-r))
    (hunit : a*b-c*r=1)
    (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
    (1:ℝ)/n < ndist ((v:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) := by sorry
