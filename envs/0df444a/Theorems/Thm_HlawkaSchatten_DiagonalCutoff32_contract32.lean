-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_contract32
-- name    : HlawkaSchatten.DiagonalCutoff32.contract32
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:19:50.127321+00:00
-- url     : https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10
-- title:
--   Residual-budget localization of a Hlawka counterexample on $[32,50]$
-- statement:
--   Let $32\le p\le 50$ and let $X$ be a real $3\times 3$ matrix with entries in the coarse box ($D=[-1.158,-0.555]$ for diagonal entries and $O=[0.79,1.158]$ for off-diagonal entries), row norms summing to $3$, $\|X_0+X_1+X_2\|_p<3q(p)$ for the slab envelope radius $q(p)$, and pair-gap sum below $2/(0.448\,p)$. Then
--
--   $$-1.065\le X_{ii}\le -0.625,\qquad 0.849\le X_{ji}\le 1.121\quad (j\ne i).$$
--
--   The proof contracts the coarse box by a residual-budget argument with a finite-$p$ two-coordinate cost, certified uniformly on sub-slabs of exponents.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff32_SlabRadius
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem HlawkaSchatten.DiagonalCutoff32.contract32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 → ∀ X : Triple,
    (∀ j i : Fin 3, if j = i then -(1158/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555/1000 : ℝ)
      else (79/100 : ℝ) ≤ X j i ∧ X j i ≤ (1158/1000 : ℝ)) →
    lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
    lpNorm p (X 0 + X 1 + X 2) < 3 * slabRadius p →
    pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448/1000) * p) →
    ∀ j i : Fin 3, if j = i then -(1065/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(625/1000 : ℝ)
      else (849/1000 : ℝ) ≤ X j i ∧ X j i ≤ (1121/1000 : ℝ) := by sorry
