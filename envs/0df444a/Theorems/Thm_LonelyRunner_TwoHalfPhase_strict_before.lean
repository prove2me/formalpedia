-- Prove2me | Theorems.Thm_LonelyRunner_TwoHalfPhase_strict_before
-- name    : LonelyRunner.TwoHalfPhase.strict_before
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:16.856525+00:00
-- url     : https://prove2.me/theorems/9cafb29c-758e-4e8d-9350-3a6174d70e22
-- title:
--   Two half-phase speeds escape within a universal clock ratio
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For real $n,a,b,L$ with $n\ge10$, $0<a<b$, and $L>((n+2)/(n-2))^2$, there exists $z\in(1,L)$ with $d(1/2-az/n)>1/n$ and $d(1/2-bz/n)>1/n$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/TwoHalfPhase.lean, lines 256–290, declaration LonelyRunner.TwoHalfPhase.strict_before. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.TwoHalfPhase
open TwoBlockerArithmetic

/-- With any open upper bound beyond Z², two half-phase runners have an
actual strictly safe clock between 1 and that bound. No band-chain or
component certificate is assumed. -/
theorem LonelyRunner.TwoHalfPhase.strict_before {n slow fast L : ℝ}
    (hn : 10 ≤ n) (hslow : 0 < slow) (horder : slow < fast)
    (hL : ((n+2)/(n-2))^2 < L) :
    ∃z ∈ Set.Ioo 1 L,
      1/n < ndist (1/2-slow*z/n) ∧ 1/n < ndist (1/2-fast*z/n) := by sorry
