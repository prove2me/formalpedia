-- Prove2me | Theorems.Thm_LonelyRunner_LargeDeletionMatching_common_insertion_obstruction
-- name    : LonelyRunner.LargeDeletionMatching.common_insertion_obstruction
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:36.978394+00:00
-- url     : https://prove2.me/theorems/e5af090f-7208-4a56-8ae7-e069d3b8dd47
-- title:
--   Two-deletion configurations cannot have the specified shared insertion at equality
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Let $n,r,s,p,q\in\mathbb N$ satisfy $n\ge5$, $n\le2r$, $r<s<n\le p<q$, and $\gcd(r,s)\ge2$. If either $r\mid p$ and $s\mid p$, or $r\mid q$, $s\mid q$, and $r\nmid p$, then
--
--   $$S(n,\{r,s\},\{p,q\})\text{ has a strict time}.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/LargeDeletionMatching.lean, lines 70–196, declaration LonelyRunner.LargeDeletionMatching.common_insertion_obstruction. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.LargeDeletionMatching
open BadCover SingleDeletion

set_option maxHeartbeats 1200000 in

theorem LonelyRunner.LargeDeletionMatching.common_insertion_obstruction {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hg : 2 ≤ Nat.gcd r s)
    (hno : ¬ HasStrictTime n r s p q)
    (hcommon : (r ∣ p ∧ s ∣ p) ∨ (r ∣ q ∧ s ∣ q ∧ ¬r ∣ p)) : False := by sorry
