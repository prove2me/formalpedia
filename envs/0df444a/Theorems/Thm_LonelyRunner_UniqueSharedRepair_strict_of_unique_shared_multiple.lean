-- Prove2me | Theorems.Thm_LonelyRunner_UniqueSharedRepair_strict_of_unique_shared_multiple
-- name    : LonelyRunner.UniqueSharedRepair.strict_of_unique_shared_multiple
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:50.856994+00:00
-- url     : https://prove2.me/theorems/570b129f-51ed-4951-ad0f-6fff3818c792
-- title:
--   Any-order unique shared repair with at most three insertions
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,P\in\mathbb N$ and let $R,W\subseteq\mathbb N$ be finite. Assume $r\ge7$, $n\le2r$, $r<s<n$, $r\in R$, $P\in W$, every member of $W$ is positive, $|W|\le3$, $r\mid P$, $s\mid P$, and $r$ divides no member of $W\setminus\{P\}$. Then $S(n,R,W)$ has a strict time. The sizes and relative order of the inserted speeds are unrestricted. The larger divisor $s$ need not belong to $R$. This is a strictness theorem for the stated structured speed sets; it does not resolve the general lonely runner conjecture.
--
--   AI-assisted research and formalization. The Lean proof is machine-checked; independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/UniqueSharedRepair.lean, lines 59–82, declaration LonelyRunner.UniqueSharedRepair.strict_of_unique_shared_multiple. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.UniqueSharedRepair

/-- Divisibility-only formulation of the any-order theorem. Positivity and
sharedness themselves supply the positive multipliers and m>=2. -/
theorem LonelyRunner.UniqueSharedRepair.strict_of_unique_shared_multiple {n r s P : ℕ} {R W : Finset ℕ}
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hP : P ∈ W) (hpos : ∀v ∈ W, 0 < v)
    (hcard : W.card ≤ 3) (hrP : r ∣ P) (hsP : s ∣ P)
    (hunique : ∀v ∈ W.erase P, ¬r ∣ v) :
    SeparatedMulti.HasStrictTime n R W := by sorry
