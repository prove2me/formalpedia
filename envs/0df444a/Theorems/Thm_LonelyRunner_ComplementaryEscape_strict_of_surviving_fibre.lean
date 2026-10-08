-- Prove2me | Theorems.Thm_LonelyRunner_ComplementaryEscape_strict_of_surviving_fibre
-- name    : LonelyRunner.ComplementaryEscape.strict_of_surviving_fibre
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:22.211285+00:00
-- url     : https://prove2.me/theorems/ac53e2cd-472a-40ff-b3d5-edfa431b57a0
-- title:
--   A surviving primitive fibre yields a strict time
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $U_r=\{0\le b<r:\gcd(r,b)=1\}$, $F_{n,r}=\{n-r\le b<n:\gcd(r,b)=1\}$, and $B(n,r,m,q,b)$ for the existence of an integer $D$ with $|nmD-q|\le mr$ and $r\mid Db-q$. An active fibre for $(n,r,m,q)$ consists of natural numbers $(d,h,U,V)$ with $d,V>0$, $h\ge2$, $r=dh$, $q=dU$, $\gcd(h,U)=\gcd(h,V)=1$, $|nmV-U|\le hm$, and, for every $b\in U_r$, $B(n,r,m,q,b)$ if and only if $h\mid Vb-U$. Let $F,G$ be active fibres for $(n,r,m,q)$ and $(n,r,m,u)$. Assume $r\ge7$, $r+2\le n\le2r$, $m>0$, $r\in R$, $mr<q<u$, $F.h,G.h\in\{3,4,6\}$, and either $n\ge12$ or $F.h=4$. Suppose $B(n,r,m,u,c)$ implies $\neg B(n,r,m,q,c)$ for every $c\in U_r$. If some $b\in F_{n,r}$ satisfies $G.h\mid G.Vb-G.U$ and $b((nG.V/G.h+1)/(u/(mr)))<m(n-r)$, then $S(n,R,\{mr,q,u\})$ has a strict time. The quotients in the margin condition are real.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/ComplementaryEscape.lean, lines 114–176, declaration LonelyRunner.ComplementaryEscape.strict_of_surviving_fibre. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.ComplementaryEscape
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm

/-- All geometric hypotheses of an escape are derived from the active
small-fibre certificates; only the selected flank's arithmetic margin remains. -/
theorem LonelyRunner.ComplementaryEscape.strict_of_surviving_fibre {n r m q u b : ℕ} {R : Finset ℕ}
    (F : ActiveFibre n r m q) (G : ActiveFibre n r m u)
    (hr : 7 ≤ r) (hrmax : r+2 ≤ n) (hm : 0 < m) (hrR : r ∈ R)
    (hlarge : n ≤ 2*r) (hpq : m*r < q) (hqu : q < u)
    (hF : F.h=3 ∨ F.h=4 ∨ F.h=6) (hG : G.h=3 ∨ G.h=4 ∨ G.h=6)
    (hsize : 12 ≤ n ∨ F.h=4)
    (hcomp : ∀c ∈ units r, CollectiveBoundary.Blocks (n:ℤ) r m u c →
      ¬CollectiveBoundary.Blocks (n:ℤ) r m q c)
    (hb : b ∈ primitiveFlanks n r) (hbg : (G.h:ℤ) ∣ (G.V:ℤ)*b-G.U)
    (hmargin : (b:ℝ)*(((n:ℝ)*G.V/G.h+1)/((u:ℝ)/((m:ℝ)*r))) <
      (m:ℝ)*((n:ℝ)-r)) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by sorry
