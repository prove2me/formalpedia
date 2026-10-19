-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_certified_nonneg21_chunk08
-- name    : HlawkaSchatten.DiagonalCutoff21.certified_nonneg21_chunk08
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-17T12:45:26.235869+00:00
-- url     : https://prove2.me/theorems/bb6a9979-7e2b-4215-b1ed-31a654630226
-- title:
--   Actual-norm localized nonnegativity [25,51/2]
-- statement:
--   For every real p in [25,51/2], any real three-by-three triple in the stated coarse coordinate box, whose singleton norms sum to three, total norm is below 3033/2500, and original pair-gap sum is below 2/((273/625)p), has nonnegative original Hlawka deficit for the unchanged cyclic constant. Unequal singleton norms are allowed. The proof internally checks sixteen complete contraction schedules, all root and budget premises, the actual norm-Hessian estimates, convexity and simultaneous permutation averaging. This is the localization-to-nonnegativity step, not the original unrestricted real-three theorem.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 4-7, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic norm and averaging proofs by Ezzeri Esa; contraction framework adapted from @bwdaugherty; Apache-2.0 notices retained.

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Topology.Order.Compact
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_scalar_window26
import Mathlib.Analysis.Complex.ExponentialBounds
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.certified_nonneg21_chunk08 :
    ∀ p : ℝ, (25 : ℝ) ≤ p → p ≤ (51/2 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
