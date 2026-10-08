-- Prove2me | Theorems.Thm_LonelyRunner_MatchingArithmetic_full_width
-- name    : LonelyRunner.MatchingArithmetic.full_width
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:39.49099+00:00
-- url     : https://prove2.me/theorems/2a2a3369-76e1-453f-a4d7-859de5c18710
-- title:
--   The shared-repair cover bound is smaller than the available baseline interval
-- statement:
--   Let $n,r,s,g,w,F\in\mathbb R$ satisfy $2\le g$, $2g\le r$, $r+g\le s$, $s+1\le n$, $w>0$, and $rs\le gw$. Assume either $n\le2r-1$ and $F=r-1$, or $n=2r$ and $F=2r-1$. Then
--
--   $$\frac{2}{nw}\left(1+\frac4{n-2}\right)<\frac{n-r}{nr(r+1)}+\frac{n-r}{nrF}.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/MatchingArithmetic.lean, lines 30–98, declaration LonelyRunner.MatchingArithmetic.full_width. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.MatchingArithmetic

set_option maxHeartbeats 1000000 in

theorem LonelyRunner.MatchingArithmetic.full_width {n r s g w F : ℝ}
    (hg : 2 ≤ g) (hrg : 2*g ≤ r) (hgs : r+g ≤ s) (hsn : s+1 ≤ n)
    (hw : 0 < w) (hmul : r*s ≤ g*w)
    (hF : (n ≤ 2*r-1 ∧ F=r-1) ∨ (n=2*r ∧ F=2*r-1)) :
    (2*(1/n)/w)*(1+4/(n-2)) <
      (n-r)/(n*r*(r+1)) + (n-r)/(n*r*F) := by sorry
