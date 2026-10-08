-- Prove2me | Theorems.Thm_LonelyRunner_CoprimeReplacements_not_covered
-- name    : LonelyRunner.CoprimeReplacements.not_covered
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:55.114325+00:00
-- url     : https://prove2.me/theorems/767115d6-2d2b-422b-a14b-e7cc9cfa49f8
-- title:
--   Two large inserted speeds cannot cover a Farey-adjacent interval
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. Let $a,b,n,r,s,p,q\in\mathbb Z$ satisfy $br-as=1$, $n\ge5$, and $0<r<s<n\le p<q$. All fractions are real. Then
--
--   $$\neg\bigl(\forall t\in[a/r,b/s],\ d(pt)\le1/n\ \lor\ d(qt)\le1/n\bigr).$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/CoprimeReplacements.lean, lines 159–318, declaration LonelyRunner.CoprimeReplacements.not_covered. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.CoprimeReplacements
open Farey BadCover

set_option maxHeartbeats 1200000 in

theorem LonelyRunner.CoprimeReplacements.not_covered {a b n r s p q : ℤ}
    (h : b * r - a * s = 1) (hn : 5 ≤ n) (hr : 0 < r)
    (hrs : r < s) (hsn : s < n) (hnp : n ≤ p) (hpq : p < q) :
    ¬ (∀ t ∈ Set.Icc ((a : ℝ) / r) ((b : ℝ) / s),
      ndist ((p : ℝ) * t) ≤ 1 / n ∨ ndist ((q : ℝ) * t) ≤ 1 / n) := by sorry
