-- Prove2me | Theorems.Thm_LonelyRunner_ComponentRestoration_safe_segment
-- name    : LonelyRunner.ComponentRestoration.safe_segment
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:23.696219+00:00
-- url     : https://prove2.me/theorems/ffd38c8e-010c-4fcf-950f-8d3253ec1951
-- title:
--   Strict safety persists along a nearby rational-center segment
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $n,r,v\in\mathbb N$, $a\in\mathbb Z$, and $t,u\in\mathbb R$. Assume $0<r<n$, $v<n$, $d(va/r)\ge1/r$, $|rt-a|\le1/n$, and $d(vt)>1/n$. If $u$ is between $t$ and $a/r$, then
--
--   $$d(vu)>1/n.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/ComponentRestoration.lean, lines 77–131, declaration LonelyRunner.ComponentRestoration.safe_segment. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.ComponentRestoration
open SeparatedMulti InteractionComponents


theorem LonelyRunner.ComponentRestoration.safe_segment {n r v : ℕ} {a : ℤ} {t u : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrn : r < n) (hvn : v < n)
    (hcenter : 1/(r:ℝ) ≤ ndist ((v:ℝ)*((a:ℝ)/r)))
    (hbad : |(r:ℝ)*t-a| ≤ 1/(n:ℝ))
    (hsafe : 1/(n:ℝ) < ndist ((v:ℝ)*t))
    (hu : u ∈ Set.Icc (min t ((a:ℝ)/r)) (max t ((a:ℝ)/r))) :
    1/(n:ℝ) < ndist ((v:ℝ)*u) := by sorry
