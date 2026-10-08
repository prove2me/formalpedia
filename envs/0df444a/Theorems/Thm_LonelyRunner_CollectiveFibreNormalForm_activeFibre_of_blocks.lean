-- Prove2me | Theorems.Thm_LonelyRunner_CollectiveFibreNormalForm_activeFibre_of_blocks
-- name    : LonelyRunner.CollectiveFibreNormalForm.activeFibre_of_blocks
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:48.330795+00:00
-- url     : https://prove2.me/theorems/3c130f5d-3644-48eb-811b-b0f2f7061439
-- title:
--   A noncoprime active blocker has a reduced congruence fibre
-- statement:
--   Write $U_r=\{0\le b<r:\gcd(r,b)=1\}$, $F_{n,r}=\{n-r\le b<n:\gcd(r,b)=1\}$, and $B(n,r,m,q,b)$ for the existence of an integer $D$ with $|nmD-q|\le mr$ and $r\mid Db-q$. An active fibre for $(n,r,m,q)$ consists of natural numbers $(d,h,U,V)$ with $d,V>0$, $h\ge2$, $r=dh$, $q=dU$, $\gcd(h,U)=\gcd(h,V)=1$, $|nmV-U|\le hm$, and, for every $b\in U_r$, $B(n,r,m,q,b)$ if and only if $h\mid Vb-U$. For natural $n,r,m,q$, assume $0<r<n$, $m>0$, $mr<q$, $r\nmid q$, $\gcd(r,q)\ne1$, and $B(n,r,m,q,b)$ for some $b\in U_r$. Then an active fibre for $(n,r,m,q)$ exists.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/CollectiveFibreNormalForm.lean, lines 30–106, declaration LonelyRunner.CollectiveFibreNormalForm.activeFibre_of_blocks. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.CollectiveFibreNormalForm

theorem LonelyRunner.CollectiveFibreNormalForm.activeFibre_of_blocks {n r m q : ℕ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hqp : m*r < q)
    (hnot : ¬ r ∣ q) (hcop : ¬ Nat.Coprime r q)
    (hactive : ∃ b ∈ CollectiveUnits.units r,
      CollectiveBoundary.Blocks (n:ℤ) r m q b) :
    Nonempty (ActiveFibre n r m q) := by sorry
