-- Prove2me | Theorems.Thm_LonelyRunner_BadCover_slow_center_gap
-- name    : LonelyRunner.BadCover.slow_center_gap
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:55:01.666373+00:00
-- url     : https://prove2.me/theorems/e88ce790-1f55-4f22-ab59-6c4c1668b5d2
-- title:
--   Covering an interior slow-center band forces a speed-ratio inequality
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $A,B,p,q,\delta,x\in\mathbb R$ and $c\in\mathbb Z$, with $0<p<q$ and $0<\delta\le1/5$. Assume $px=c$, $d(qx)>\delta$, $A<x-\delta/p$, $x+\delta/p<B$, and $d(pt)\le\delta$ or $d(qt)\le\delta$ for every $t\in[A,B]$. Then
--
--   $$(1-2\delta)p\le2\delta q.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/MatchingGeometry.lean, lines 63–119, declaration LonelyRunner.BadCover.slow_center_gap. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.BadCover


theorem LonelyRunner.BadCover.slow_center_gap {A B p q δ x : ℝ} {c : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5*δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hc : p*x = c) (hsafe : δ < ndist (q*x))
    (hleft : A < x-δ/p) (hright : x+δ/p < B) :
    (1-2*δ)*p ≤ 2*δ*q := by sorry
