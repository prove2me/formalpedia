-- Prove2me | Theorems.Thm_LonelyRunner_SharedFastest_strict_of_shared_fastest
-- name    : LonelyRunner.SharedFastest.strict_of_shared_fastest
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:23.83892+00:00
-- url     : https://prove2.me/theorems/6dd7ae2f-8361-48b1-a50c-a6f4edf97c59
-- title:
--   A unique shared fastest repair forces strictness
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,m,k\in\mathbb N$ and $P=mr=ks$. Assume $n\ge5$, $r\ge7$, $n\le2r$, $r<s<n$, $r\in R$, $m\ge2$, $k>0$, $P\in W$, $W$ is positive, $|W|\le3$, every member of $W\setminus\{P\}$ is less than $P$, and none is divisible by $r$. Then $S(n,R,W)$ has a strict time.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/SharedFastest.lean, lines 113–125, declaration LonelyRunner.SharedFastest.strict_of_shared_fastest. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.SharedFastest
open FastestBoundary

/-- If the fastest insertion is shared by r<s and uniquely supplies r>=7,
at most three insertions cannot prevent a strictly lonely time. -/
theorem LonelyRunner.SharedFastest.strict_of_shared_fastest {n r s m k : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hr : 7 ≤ r) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hm : 2 ≤ m) (hk : 0 < k) (heq : m*r=k*s)
    (hpW : m*r ∈ W) (hW : ∀ q ∈ W, 0 < q)
    (hmax : ∀ q ∈ W.erase (m*r), q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬ r ∣ q)
    (hcard : W.card ≤ 3) : SeparatedMulti.HasStrictTime n R W := by sorry
