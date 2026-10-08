-- Prove2me | Theorems.Thm_LonelyRunner_SharedSlowest_strict_of_shared_slowest
-- name    : LonelyRunner.SharedSlowest.strict_of_shared_slowest
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T06:04:26.107618+00:00
-- url     : https://prove2.me/theorems/304cc8e9-1cb6-44db-aebe-ab1617ee7b2b
-- title:
--   A unique shared slowest repair with two faster insertions forces strictness
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,m,k,q,u\in\mathbb N$. Assume $r\ge7$, $n\le2r$, $r<s<n$, $r\in R$, $m\ge2$, $k>0$, $mr=ks$, $mr<q<u$, $r\nmid q$, and $r\nmid u$. Then $S(n,R,\{mr,q,u\})$ has a strict time.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc, lean/LonelyRunner/SharedSlowest.lean, lines 70–107, declaration LonelyRunner.SharedSlowest.strict_of_shared_slowest. AI-assisted formalization. The snapshot identifier records the submitted local source; it is not a claim that this commit is publicly hosted.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_LRC_SharedRepair_Defs

open LonelyRunner
open LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm

/-- **Shared slowest repair theorem.** No upper bound on either faster speed
or the multiplier is imposed. The conclusion is a real strict lonely time
for every retained baseline speed and all three insertions. -/
theorem LonelyRunner.SharedSlowest.strict_of_shared_slowest {n r s m k q u : ℕ} {R : Finset ℕ}
    (hr : 7 ≤ r) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hrR : r ∈ R) (hm : 2 ≤ m) (hk : 0 < k) (hshared : m*r=k*s)
    (hpq : m*r < q) (hqu : q < u) (hnq : ¬r ∣ q) (hnu : ¬r ∣ u) :
    SeparatedMulti.HasStrictTime n R {m*r,q,u} := by sorry
