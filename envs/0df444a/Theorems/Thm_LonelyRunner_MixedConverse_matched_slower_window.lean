-- Prove2me | Theorems.Thm_LonelyRunner_MixedConverse_matched_slower_window
-- name    : LonelyRunner.MixedConverse.matched_slower_window
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:29.254002+00:00
-- url     : https://prove2.me/theorems/2ed960c4-7c9f-40cc-afb5-4c342f4002b4
-- title:
--   The slower matched insertion must obey its GW window
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $\operatorname{GW}(n,r,m)$ for the assertion that no natural number $b$ with $n-r\le b<m(n-r)$ is coprime to $r$. Let $n,r,s,m,k\in\mathbb N$ satisfy $n\ge5$, $n\le2r$, $n\le2s$, $r,s<n$, $r\ne s$, and $n\le mr<ks$. Then
--
--   $$S(n,\{r,s\},\{mr,ks\})\text{ has no strict time}\ \Longrightarrow\ \operatorname{GW}(n,r,m).$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/MixedConverse.lean, lines 10–189, declaration LonelyRunner.MixedConverse.matched_slower_window. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.MixedConverse
open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction

set_option maxHeartbeats 3000000 in

theorem LonelyRunner.MixedConverse.matched_slower_window {n r s m k : ℕ}
    (hn : 5 ≤ n) (hrlarge : n ≤ 2*r) (hslarge : n ≤ 2*s)
    (hrn : r < n) (hsn : s < n) (hrs : r ≠ s)
    (hnp : n ≤ m*r) (hpq : m*r < k*s)
    (hno : ¬ HasStrictTime n r s (m*r) (k*s)) : GW n r m := by sorry
