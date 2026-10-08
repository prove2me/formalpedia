-- Prove2me | Theorems.Thm_LonelyRunner_CollectiveBoundaryForcing_second_fastest_forces_parity
-- name    : LonelyRunner.CollectiveBoundaryForcing.second_fastest_forces_parity
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:03:58.323259+00:00
-- url     : https://prove2.me/theorems/5d6c5f00-093c-46ee-b544-b24ff7b31133
-- title:
--   A complete primitive cover forces an active half-phase blocker
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $U_r=\{0\le b<r:\gcd(r,b)=1\}$, $F_{n,r}=\{n-r\le b<n:\gcd(r,b)=1\}$, and $B(n,r,m,q,b)$ for the existence of an integer $D$ with $|nmD-q|\le mr$ and $r\mid Db-q$. Let $n,r,m,Q,\ell\in\mathbb N$, $P=mr$, and $W$ be positive. Assume $n\ge5$, $r\in R$, $r<n\le2r$, $m\ge2$, $n\le m(n-r)$, $P,Q\in W$, $P<Q$, every member of $W\setminus\{P,Q\}$ is less than $P$, and $P$ is the unique member of $W$ divisible by $r$. If $\ell\ge3$, $|W|\le\ell$, $\varphi(r)\ge2\ell-2$, and no strict time exists, then $r\mid2Q$ and some $b\in F_{n,r}$ satisfies $B(n,r,m,Q,b)$.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/CollectiveBoundaryForcing.lean, lines 26–131, declaration LonelyRunner.CollectiveBoundaryForcing.second_fastest_forces_parity. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.CollectiveBoundaryForcing
open CollectiveBoundary CollectiveUnits

/-- With at most `ell` insertions, a unique second-fastest repair can cover a
full primitive period only when its faster insertion has half-integer phase.
The returned primitive boundary also certifies that this fast band is active. -/
theorem LonelyRunner.CollectiveBoundaryForcing.second_fastest_forces_parity {n r m Q ell : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hfull : n ≤ m*(n-r))
    (hP : m*r ∈ W) (hQ : Q ∈ W) (hpq : m*r < Q)
    (hWpos : ∀ q ∈ W, 0 < q)
    (hslow : ∀ q ∈ (W.erase (m*r)).erase Q, q < m*r)
    (hunique : ∀ q ∈ W.erase (m*r), ¬r ∣ q)
    (hell : 3 ≤ ell) (hcard : W.card ≤ ell)
    (hphi : 2*ell-2 ≤ r.totient)
    (hno : ¬ SeparatedMulti.HasStrictTime n R W) :
    (r ∣ 2*Q) ∧ ∃ b ∈ primitiveFlanks n r,
      Blocks (n:ℤ) r m Q b := by sorry
