-- Prove2me | Theorems.Thm_LonelyRunner_SmallComponentRigidity_matching_windows
-- name    : LonelyRunner.SmallComponentRigidity.matching_windows
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:31.446002+00:00
-- url     : https://prove2.me/theorems/402bc547-be7e-4b30-bb4c-8552f4151286
-- title:
--   GW matching is forced when insertion components have size at most two
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $\operatorname{GW}(n,r,m)$ for the assertion that no natural number $b$ with $n-r\le b<m(n-r)$ is coprime to $r$. A separated cut $C\subseteq W$ satisfies $p+q<n\gcd(p,q)$ for every $p\in C$ and $q\in W\setminus C$. The insertion-component hypothesis means that $W$ admits a finite partition into blocks of size at most two, each a separated cut. Equivalently, the graph joining distinct $p,q$ when $n\gcd(p,q)\le p+q$ has components of size at most two. Assume $n\ge5$, $n\le2r$ and $r<n$ for every $r\in R$, every $p\in W$ is at least $n$, $|R|=|W|$, the insertion-component hypothesis holds, and $S(n,R,W)$ has no strict time. Then
--
--   $$\exists\text{ a bijection }f:R\to W\ \forall r\in R\ \exists m_r\ge2:\quad f(r)=m_rr\ \land\operatorname{GW}(n,r,m_r).$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/SmallComponentRigidity.lean, lines 143–218, declaration LonelyRunner.SmallComponentRigidity.matching_windows. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.SmallComponentRigidity
open SeparatedMulti SeparatedReplacements InteractionComponents


theorem LonelyRunner.SmallComponentRigidity.matching_windows {n : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hW : ∀ p ∈ W, n ≤ p) (hparts : PairComponents n W)
    (hcard : R.card=W.card) (hno : ¬ HasStrictTime n R W) :
    ∃ f : ℕ → ℕ, Set.BijOn f (R : Set ℕ) (W : Set ℕ) ∧
      ∀ r ∈ R, ∃ m : ℕ, 2 ≤ m ∧ f r=m*r ∧ GW n r m := by sorry
