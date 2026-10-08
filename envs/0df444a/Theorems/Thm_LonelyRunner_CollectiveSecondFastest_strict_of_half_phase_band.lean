-- Prove2me | Theorems.Thm_LonelyRunner_CollectiveSecondFastest_strict_of_half_phase_band
-- name    : LonelyRunner.CollectiveSecondFastest.strict_of_half_phase_band
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:07:37.767302+00:00
-- url     : https://prove2.me/theorems/b6774577-1db0-448e-9078-9c6259f8f90b
-- title:
--   An active half-phase band admits a strict escape
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,m,Q\in\mathbb N$, $P=mr$, and let $W$ contain only positive speeds. Assume $n\ge5$, $r>0$, $r+2\le n\le2r$, $r\in R$, $m\ge2$, $n<m(n-r)$, $P<Q$, $Q\in W$, every member of $W\setminus\{P,Q\}$ is less than $P$, and no member of $W\setminus\{P\}$ is divisible by $r$. Assume also $|W\setminus\{P,Q\}|+1<\varphi(r)$, $r\mid2Q$, and $d(1/2-Q/(nmr))\le1/n$. Then $S(n,R,W)$ has a strict time. Membership of $P$ in $W$ is not required.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/CollectiveSecondFastest.lean, lines 211–303, declaration LonelyRunner.CollectiveSecondFastest.strict_of_half_phase_band. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.CollectiveSecondFastest
open BadCover

/-- Once the canonical cover has forced the half-phase resonance, its common
band exit supplies a strict time. This is the geometric half of the theorem. -/
theorem LonelyRunner.CollectiveSecondFastest.strict_of_half_phase_band {n r m Q : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hr : 0 < r) (hrmax : r+2 ≤ n) (hm : 2 ≤ m)
    (hrR : r ∈ R) (hlarge : n ≤ 2*r)
    (hfull : n < m*(n-r)) (hpq : m*r < Q)
    (hWpos : ∀p ∈ W, 0 < p)
    (hslow : ∀p ∈ (W.erase (m*r)).erase Q, p < m*r)
    (hunique : ∀p ∈ W.erase (m*r), ¬r ∣ p)
    (hQ : Q ∈ W) (hcount : ((W.erase (m*r)).erase Q).card+1 < r.totient)
    (hd : r ∣ 2*Q)
    (hband : ndist (1/2-((Q:ℝ)/((m:ℝ)*r))/(n:ℝ)) ≤ 1/(n:ℝ)) :
    SeparatedMulti.HasStrictTime n R W := by sorry
