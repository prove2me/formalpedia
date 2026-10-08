-- Prove2me | Theorems.Thm_LonelyRunner_ShiftedBlocks_length_le_of_one_slow
-- name    : LonelyRunner.ShiftedBlocks.length_le_of_one_slow
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:10.860371+00:00
-- url     : https://prove2.me/theorems/4b0c454a-80cc-4263-8403-99e0af07fe18
-- title:
--   Length bound for a cover using one fixed slow band
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $A,B,p,q,\alpha,\beta,\delta,u\in\mathbb R$ and $c\in\mathbb Z$, with $p,q>0$, $0\le\delta<1/2$, $u\in[A,B]$, and $|\alpha+pu-c|\le\delta$. Suppose every $t\in[A,B]$ satisfies either $|\alpha+pt-c|\le\delta$ or $d(\beta+qt)\le\delta$. Put $a=2\delta/p+2\delta/q$. Then $B-A\le\max\{a,(\lfloor qa\rfloor+2\delta)/q\}$. No ordering between $p$ and $q$ is assumed.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/ShiftedBlocks.lean, lines 87–160, declaration LonelyRunner.ShiftedBlocks.length_le_of_one_slow. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.ShiftedBlocks

theorem LonelyRunner.ShiftedBlocks.length_le_of_one_slow {A B p q α β δ u : ℝ} {c : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ : δ < 1/2)
    (hu : u ∈ Set.Icc A B) (hc : |α+p*u-c| ≤ δ)
    (hcover : ∀ t ∈ Set.Icc A B, |α+p*t-c| ≤ δ ∨ ndist (β+q*t) ≤ δ) :
    B-A ≤ blockBound p q δ := by sorry
