-- Prove2me | Theorems.Thm_LonelyRunner_TwoHalfPhase_ratio_of_one_slow
-- name    : LonelyRunner.TwoHalfPhase.ratio_of_one_slow
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:11.920882+00:00
-- url     : https://prove2.me/theorems/962807b0-a4b1-4e23-9c28-2e7c48db3437
-- title:
--   A single slow band limits the multiplicative stretch of a half-phase cover
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $n,p,q,A,B,u,T\in\mathbb R$ with $n\ge8$, $0<p<q$, $0<A\le B$, $u\in[A,B]$, $T\ge1/2$, and $|pu-T|\le1/n$. If every $z\in[A,B]$ satisfies either $|pz-T|\le1/n$ or $d(-1/2+qz)\le1/n$, then $B\le((n+2)/(n-2))^2A$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/TwoHalfPhase.lean, lines 58–207, declaration LonelyRunner.TwoHalfPhase.ratio_of_one_slow. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.TwoHalfPhase
open TwoBlockerArithmetic

set_option maxHeartbeats 800000 in
/-- A cover involving one fixed slow band has the universal half-phase ratio.
The fast bands on either side are obtained from interval coverage, not supplied
as a certificate. -/
theorem LonelyRunner.TwoHalfPhase.ratio_of_one_slow {n p q A B u T : ℝ}
    (hn : 8 ≤ n) (hp : 0 < p) (hpq : p < q)
    (hA : 0 < A) (_hAB : A ≤ B) (hu : u ∈ Set.Icc A B)
    (hT : 1/2 ≤ T) (huT : |p*u-T| ≤ 1/n)
    (hcover : ∀z ∈ Set.Icc A B,
      |p*z-T| ≤ 1/n ∨ ndist (-1/2+q*z) ≤ 1/n) :
    B ≤ ((n+2)/(n-2))^2*A := by sorry
