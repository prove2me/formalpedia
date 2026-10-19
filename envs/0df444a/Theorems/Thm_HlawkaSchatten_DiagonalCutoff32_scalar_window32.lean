-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_scalar_window32
-- name    : HlawkaSchatten.DiagonalCutoff32.scalar_window32
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:19:55.627602+00:00
-- url     : https://prove2.me/theorems/9bf2147a-5bfb-4608-98df-4ae448f55641
-- title:
--   Scalar window for the sharp diagonal Hlawka constant on $[32,50]$
-- statement:
--   Let $K_p$ denote the cyclic constant of the foundation mission and $\mathrm{scalarEnvelope}(p,q)$ its scalar envelope. For every real exponent $p$ with $32\le p\le 50$:
--
--   $$0.448\,p<K_p,\qquad \mathrm{scalarEnvelope}(p,0.386)<K_p,\qquad K_p\le \frac p2.$$
--
--   These three scalar facts confine a normalized counterexample to Hlawka's inequality with constant $K_p$: the linear lower bound controls the pair-gap sum, the envelope bound controls the total norm, and the upper bound limits the constant in the convexity estimate.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff32.scalar_window32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (386 / 1000) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
