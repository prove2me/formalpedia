-- Prove2me | Theorems.Thm_LonelyRunner_FailedFlank_baseline_safe_offset
-- name    : LonelyRunner.FailedFlank.baseline_safe_offset
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:10.067155+00:00
-- url     : https://prove2.me/theorems/480dbf4d-6df8-4d06-ae1c-c4072d559f75
-- title:
--   A short primitive flank preserves all retained baseline speeds
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $n,r,b,a,c,v\in\mathbb Z$ and $e\in\mathbb R$. Assume $0<r<n\le2r$, $n-r\le b$, $ab-cr=1$, $0<v<n$, $v\ne r$, $0<e<1/(nr)$, and $eb<(n-r)/(nr)$. Then $d(v(a/r-e))>1/n$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/FailedFlank.lean, lines 14–87, declaration LonelyRunner.FailedFlank.baseline_safe_offset. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.FailedFlank
open Farey BadCover LargeDeletionMatching

set_option maxHeartbeats 1000000 in
/-- Every retained baseline speed is safe strictly inside the left half of
the single-deletion component specified by the inverse of b modulo r. -/
theorem LonelyRunner.FailedFlank.baseline_safe_offset {n r b a c v : ℤ} {e : ℝ}
    (hr : 0 < r) (hrn : r < n) (hlarge : n ≤ 2*r) (hab : n-r ≤ b)
    (hunit : a*b-c*r=1) (hv : 0 < v) (hvn : v < n) (hne : v ≠ r)
    (he : 0 < e) (hemax : e < 1/((n:ℝ)*r))
    (heb : e*b < ((n:ℝ)-r)/((n:ℝ)*r)) :
    (1:ℝ)/n < ndist ((v:ℝ)*((a:ℝ)/r-e)) := by sorry
