-- Prove2me | Theorems.Thm_LonelyRunner_SeparatedMulti_minimal_multiple_gw
-- name    : LonelyRunner.SeparatedMulti.minimal_multiple_gw
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:39.884572+00:00
-- url     : https://prove2.me/theorems/f4fd3e9b-9dfa-410c-9440-d712dbc664fb
-- title:
--   The smallest repair in a separated insertion set obeys its GW window
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $\operatorname{GW}(n,r,m)$ for the assertion that no natural number $b$ with $n-r\le b<m(n-r)$ is coprime to $r$. Let $n,r,m\in\mathbb N$ with $n\ge5$, $r\in R$, $n\le2r$, $r<n$, and $m\ge2$. Suppose $mr\in W$, every $q\in W$ is at least $n$, and distinct $p,q\in W$ satisfy $p+q<n\gcd(p,q)$. Assume $mr$ is no larger than any insertion divisible by $r$. Then
--
--   $$S(n,R,W)\text{ has no strict time}\ \Longrightarrow\ \operatorname{GW}(n,r,m).$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/SeparatedMulti.lean, lines 71–133, declaration LonelyRunner.SeparatedMulti.minimal_multiple_gw. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.SeparatedMulti
open SeparatedReplacements SeparatedBands SingleDeletion

set_option maxHeartbeats 1500000 in

theorem LonelyRunner.SeparatedMulti.minimal_multiple_gw {n r m : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hrR : r ∈ R) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hpW : m*r ∈ W)
    (hW : ∀ q ∈ W, n ≤ q) (hsep : Separated n W)
    (hmin : ∀ q ∈ W, r ∣ q → m*r ≤ q)
    (hno : ¬ HasStrictTime n R W) : GW n r m := by sorry
