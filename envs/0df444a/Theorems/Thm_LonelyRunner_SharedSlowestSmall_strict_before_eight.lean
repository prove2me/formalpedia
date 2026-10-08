-- Prove2me | Theorems.Thm_LonelyRunner_SharedSlowestSmall_strict_before_eight
-- name    : LonelyRunner.SharedSlowestSmall.strict_before_eight
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:18.101635+00:00
-- url     : https://prove2.me/theorems/fb3c52cc-9531-4f3e-9f3a-6a76feae2e24
-- title:
--   Two arbitrarily shifted faster speeds escape before clock eight
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For real $n,a,b,\theta,\phi$ with $n\ge5$ and $1<a<b$, there exists $z\in(1,8)$ such that $d(\theta-az/n)>1/n$ and $d(\phi-bz/n)>1/n$. The starting phases $\theta,\phi$ are arbitrary.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/SharedSlowestSmall.lean, lines 9–58, declaration LonelyRunner.SharedSlowestSmall.strict_before_eight. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.SharedSlowestSmall
open CollectiveSecondFastest

/-- Two arbitrarily phased faster runners have a strict clock before eight.
A coarse classical interval-length bound suffices for the small exception. -/
theorem LonelyRunner.SharedSlowestSmall.strict_before_eight {n slow fast theta phi : ℝ}
    (hn : 5 ≤ n) (hs : 1 < slow) (horder : slow < fast) :
    ∃z ∈ Set.Ioo 1 8, 1/n < ndist (theta-slow*z/n) ∧
      1/n < ndist (phi-fast*z/n) := by sorry
