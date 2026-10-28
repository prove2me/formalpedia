-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_shared_pair_maxima_distinct
-- name    : HlawkaSchatten.DiagonalCutoff12.shared_pair_maxima_distinct
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T00:24:48.478869+00:00
-- url     : https://prove2.me/theorems/ffa72a36-08f9-4940-8121-9375b29494b3
-- title:
--   Overlapping pair sums have distinct maximal coordinates for localized p >= 12 triples
-- statement:
--   Let $p\ge12$ and $x,y,z\in\mathbb R^3$. Put $T=\|x+y+z\|_p$ and $G=2(\|x\|_p+\|y\|_p+\|z\|_p)-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p$. Suppose
--   $$\|x\|_p+\|y\|_p+\|z\|_p=3,\qquad
--   \max(\|x\|_p,\|y\|_p,\|z\|_p)\le T\le\frac{1647}{1250},\qquad G\le\frac{401}{1000}.$$
--   If coordinate $i$ maximizes $|(x+y)_i|$ and coordinate $j$ maximizes $|(x+z)_j|$, then $i\ne j$.
--   Thus the three pair sums can be assigned distinct principal coordinates under these localization hypotheses. Establishing those hypotheses and the global Hlawka inequality are separate tasks.
-- source:
--   Original structural improvement for the sharp diagonal Hlawka cutoff-2 campaign, with cutoff 12 under investigation: https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d . Generic coordinate-norm arguments retain attribution to the Apache-2.0 Prove2Me contributions of Ezzeri Esa, bwdaugherty and Yuxuan Xu; this result is a supporting lemma, not a claim that cutoff 12 is proved.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Function
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem HlawkaSchatten.DiagonalCutoff12.shared_pair_maxima_distinct {p : ℝ} (hp : 12 ≤ p)
    (x y z : Fin 3 → ℝ) (i j : Fin 3)
    (hS : lpNorm p x+lpNorm p y+lpNorm p z = 3)
    (hx : lpNorm p x ≤ lpNorm p (x+y+z))
    (hy : lpNorm p y ≤ lpNorm p (x+y+z))
    (hz : lpNorm p z ≤ lpNorm p (x+y+z))
    (hT : lpNorm p (x+y+z) ≤ 1647/1250)
    (hG : pairGapSum (lpNorm p) x y z ≤ 401/1000)
    (hi : ∀ k, |(x+y) k| ≤ |(x+y) i|)
    (hj : ∀ k, |(x+z) k| ≤ |(x+z) j|) : i ≠ j := by sorry
