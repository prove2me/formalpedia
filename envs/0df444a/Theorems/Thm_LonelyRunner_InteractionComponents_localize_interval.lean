-- Prove2me | Theorems.Thm_LonelyRunner_InteractionComponents_localize_interval
-- name    : LonelyRunner.InteractionComponents.localize_interval
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:32.18198+00:00
-- url     : https://prove2.me/theorems/e5a279a8-a11e-43cc-8cb4-ffe6c3534b2d
-- title:
--   A covered interval localizes at a primitive center of a smallest repair
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. A separated cut $C\subseteq W$ satisfies $p+q<n\gcd(p,q)$ for every $p\in C$ and $q\in W\setminus C$. Let $n,r,m,b\in\mathbb N$ with $n,r,m>0$, $a,c\in\mathbb Z$, and $L,U\in\mathbb R$. Let $W$ be finite and positive and $C\subseteq W$ a separated cut. Assume $mr\in C$ is no larger than any member of $W$ divisible by $r$, $ab-cr=1$, and $a/r\in[L,U]$. If every $t\in[L,U]$ has $d(qt)\le1/n$ for some $q\in W$, then
--
--   $$\forall t\in[L,U],\quad\exists p\in C:\ d(pt)\le1/n.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/InteractionComponents.lean, lines 116–187, declaration LonelyRunner.InteractionComponents.localize_interval. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.InteractionComponents
open Set


theorem LonelyRunner.InteractionComponents.localize_interval {n r m b : ℕ} {a c : ℤ} {W C : Finset ℕ} {L U : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hC : C ⊆ W) (hpC : m*r ∈ C) (hW : ∀ p ∈ W, 0 < p)
    (hcut : SeparatedCut n W C)
    (hmin : ∀ q ∈ W, r ∣ q → m*r ≤ q)
    (hu : a*(b:ℤ)-c*(r:ℤ)=1)
    (hcenter : (a:ℝ)/r ∈ Icc L U)
    (hcover : ∀ t ∈ Icc L U, ∃ q ∈ W, ndist ((q:ℝ)*t) ≤ 1/(n:ℝ)) :
    ∀ t ∈ Icc L U, ∃ p ∈ C, ndist ((p:ℝ)*t) ≤ 1/(n:ℝ) := by sorry
