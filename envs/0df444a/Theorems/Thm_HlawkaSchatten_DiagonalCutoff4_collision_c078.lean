-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c078
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c078
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:01:58.358684+00:00
-- url     : https://prove2.me/theorems/3a09d9f7-650a-4bad-bbb0-97670576dbbb
-- title:
--   Hlawka collision chart 79 excluded on [4, 33/8]
-- statement:
--   For $p\in[4,33/8]$, there is no normalized triple in the ordered chart with $k=3667/2500$, $A=37167/20000$, $d=37991/50000$, coordinate orders [[0, 1, 2], [0, 1, 2], [1, 0, 2]], and signs [[1, 1, 1], [1, 1, -1], [1, 1, -1]].
--   The chart requires $\sum_i\|X_i\|_p=3$, $\|X_i\|_p\le T$, $1\le T\le A$, and $T-kP\le3-6k$, where $T=\|\sum_iX_i\|_p$ and $P=\sum_i\|\sum_{j\ne i}X_j\|_p$.
--   Within each pair, the three signed coordinates are nonnegative in decreasing order, and the largest is at least $d$ times the pair norm. Coordinate indices are zero-based. This excludes one repeated-dominant-coordinate chart; no distinctness assumption is used.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c078 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![0, 1, 2], ![1, 0, 2]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : False := by sorry
