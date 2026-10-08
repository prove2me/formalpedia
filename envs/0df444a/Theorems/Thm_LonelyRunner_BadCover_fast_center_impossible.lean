-- Prove2me | Theorems.Thm_LonelyRunner_BadCover_fast_center_impossible
-- name    : LonelyRunner.BadCover.fast_center_impossible
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:27.840108+00:00
-- url     : https://prove2.me/theorems/68e3dd50-0f91-42a2-b5a9-a6122f8a05a4
-- title:
--   An interior fast center cannot sit in a two-speed cover while the slow speed is safe
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $A,B,p,q,\delta,x\in\mathbb R$ and $k\in\mathbb Z$, with $0<p<q$ and $0<\delta\le1/5$. Suppose $qx=k$, $d(px)>\delta$, $A<x-\delta/q$, and $x+\delta/q<B$. Then
--
--   $$\neg\bigl(\forall t\in[A,B],\ d(pt)\le\delta\ \lor\ d(qt)\le\delta\bigr).$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/MatchingGeometry.lean, lines 162–219, declaration LonelyRunner.BadCover.fast_center_impossible. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.BadCover


theorem LonelyRunner.BadCover.fast_center_impossible {A B p q δ x : ℝ} {k : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5*δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hk : q*x = k) (hsafe : δ < ndist (p*x))
    (hleft : A < x-δ/q) (hright : x+δ/q < B) : False := by sorry
