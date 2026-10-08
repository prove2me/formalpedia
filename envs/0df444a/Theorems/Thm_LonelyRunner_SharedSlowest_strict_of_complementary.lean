-- Prove2me | Theorems.Thm_LonelyRunner_SharedSlowest_strict_of_complementary
-- name    : LonelyRunner.SharedSlowest.strict_of_complementary
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:23.637868+00:00
-- url     : https://prove2.me/theorems/6bc57ee4-84a1-4942-a458-fa131798e249
-- title:
--   Complementary small fibres of a shared repair force strictness
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $U_r=\{0\le b<r:\gcd(r,b)=1\}$, $F_{n,r}=\{n-r\le b<n:\gcd(r,b)=1\}$, and $B(n,r,m,q,b)$ for the existence of an integer $D$ with $|nmD-q|\le mr$ and $r\mid Db-q$. An active fibre for $(n,r,m,q)$ consists of natural numbers $(d,h,U,V)$ with $d,V>0$, $h\ge2$, $r=dh$, $q=dU$, $\gcd(h,U)=\gcd(h,V)=1$, $|nmV-U|\le hm$, and, for every $b\in U_r$, $B(n,r,m,q,b)$ if and only if $h\mid Vb-U$. Let $F,G$ be active fibres for $(n,r,m,q)$ and $(n,r,m,u)$, and let $n,r,s,m,k,q,u\in\mathbb N$. Assume $r\ge7$, $n\le2r$, $r<s<n$, $r\in R$, $m,k>0$, $mr=ks$, $mr<q<u$, and $F.h,G.h\in\{3,4,6\}$. If for every $c\in U_r$, $B(n,r,m,u,c)$ implies $\neg B(n,r,m,q,c)$, then $S(n,R,\{mr,q,u\})$ has a strict time.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/SharedSlowest.lean, lines 15–68, declaration LonelyRunner.SharedSlowest.strict_of_complementary. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm

/-- The two complementary small-fibre branches have a full strict-time proof,
including the low-totient table and the possible small-baseline handoff. -/
theorem LonelyRunner.SharedSlowest.strict_of_complementary {n r s m k q u : ℕ} {R : Finset ℕ}
    (F : ActiveFibre n r m q) (G : ActiveFibre n r m u)
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 0 < m) (hk : 0 < k) (hshared : m*r=k*s)
    (hpq : m*r < q) (hqu : q < u)
    (hF : F.h=3 ∨ F.h=4 ∨ F.h=6) (hG : G.h=3 ∨ G.h=4 ∨ G.h=6)
    (hcomp : ∀c ∈ units r, CollectiveBoundary.Blocks (n:ℤ) r m u c →
      ¬CollectiveBoundary.Blocks (n:ℤ) r m q c) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by sorry
