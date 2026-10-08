-- Prove2me | Theorems.Thm_LonelyRunner_CollectiveSecondFastest_strict_of_shared_second_fastest
-- name    : LonelyRunner.CollectiveSecondFastest.strict_of_shared_second_fastest
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:13.998837+00:00
-- url     : https://prove2.me/theorems/f6f891dc-e8fc-4e6e-8026-76440cc2545b
-- title:
--   A unique shared second-fastest repair forces strictness
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,m,k,Q,\ell\in\mathbb N$, $P=mr=ks$, with $\ell\ge3$, $|W|\le\ell$, $n\le2r$, $r<s<n$, $r\in R$, $m\ge2$, and $k>0$. Assume $W$ is positive, $P,Q\in W$, $P<Q$, every member of $W\setminus\{P,Q\}$ is less than $P$, and $P$ is the unique member of $W$ divisible by $r$. If $\varphi(r)\ge2\ell-2$, then $S(n,R,W)$ has a strict time.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/CollectiveSecondFastest.lean, lines 327–360, declaration LonelyRunner.CollectiveSecondFastest.strict_of_shared_second_fastest. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.CollectiveSecondFastest
open BadCover

/-- A unique repair shared with a larger baseline divisor cannot be the
second-fastest insertion when the primitive-unit capacity is large enough.
The conclusion is an actual strict time, with arbitrary additional deletions. -/
theorem LonelyRunner.CollectiveSecondFastest.strict_of_shared_second_fastest {n r s m k Q ell : ℕ} {R W : Finset ℕ}
    (hell : 3 ≤ ell) (hcard : W.card ≤ ell)
    (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 2 ≤ m) (hk : 0 < k) (hshared : m*r=k*s)
    (hP : m*r ∈ W) (hQ : Q ∈ W) (hpq : m*r < Q)
    (hWpos : ∀p ∈ W, 0 < p)
    (hslow : ∀p ∈ (W.erase (m*r)).erase Q, p < m*r)
    (hunique : ∀p ∈ W.erase (m*r), ¬r ∣ p)
    (hphi : 2*ell-2 ≤ r.totient) :
    SeparatedMulti.HasStrictTime n R W := by sorry
