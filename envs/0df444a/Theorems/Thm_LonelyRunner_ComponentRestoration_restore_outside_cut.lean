-- Prove2me | Theorems.Thm_LonelyRunner_ComponentRestoration_restore_outside_cut
-- name    : LonelyRunner.ComponentRestoration.restore_outside_cut
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:42.367162+00:00
-- url     : https://prove2.me/theorems/97bf6654-defa-4d75-b6e8-bb8f399668ff
-- title:
--   Restoring deletions outside a separated cut preserves absence of strict times
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. A separated cut $C\subseteq W$ satisfies $p+q<n\gcd(p,q)$ for every $p\in C$ and $q\in W\setminus C$. Let $n\ge5$, let every $r\in R$ satisfy $n\le2r$ and $r<n$, and let $W$ be positive. Suppose $D\subseteq R$, $C\subseteq W$ is a separated cut, and every $r\in D$ has a smallest positive multiple in $W$ that lies in $C$. Then
--
--   $$S(n,R,W)\text{ has no strict time}\ \Longrightarrow\ S(n,D,C)\text{ has no strict time}.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/ComponentRestoration.lean, lines 133–188, declaration LonelyRunner.ComponentRestoration.restore_outside_cut. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.ComponentRestoration
open SeparatedMulti InteractionComponents


theorem LonelyRunner.ComponentRestoration.restore_outside_cut {n : ℕ} {R W D C : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hD : D ⊆ R) (hC : C ⊆ W) (hW : ∀ p ∈ W, 0 < p)
    (hcut : SeparatedCut n W C)
    (hrepair : ∀ r ∈ D, ∃ m : ℕ, 0 < m ∧ m*r ∈ C ∧
      ∀ q ∈ W, r ∣ q → m*r ≤ q)
    (hno : ¬ HasStrictTime n R W) : ¬ HasStrictTime n D C := by sorry
