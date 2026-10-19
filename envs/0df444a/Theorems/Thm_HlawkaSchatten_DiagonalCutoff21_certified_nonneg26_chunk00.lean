-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_certified_nonneg26_chunk00
-- name    : HlawkaSchatten.DiagonalCutoff21.certified_nonneg26_chunk00
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-17T12:50:38.178168+00:00
-- url     : https://prove2.me/theorems/b6856929-5921-4355-a5a1-df6f36a01e4e
-- title:
--   Actual-norm localized nonnegativity [26,27]
-- statement:
--   For every real p in [26,27], any real three-by-three triple in the stated coarse coordinate box, whose singleton norms sum to three, total norm is below 591/500, and original pair-gap sum is below 2/((443/1000)p), has nonnegative original Hlawka deficit for the unchanged cyclic constant. Unequal singleton norms are allowed. The proof internally checks sixteen complete contraction schedules, all root and budget premises, the actual norm-Hessian estimates, convexity and simultaneous permutation averaging. This is the localization-to-nonnegativity step, not the original unrestricted real-three theorem.
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

theorem HlawkaSchatten.DiagonalCutoff21.certified_nonneg26_chunk00 :
    ∀ p : ℝ, (26 : ℝ) ≤ p → p ≤ (27 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ)) →
      (∀ j i, j ≠ i → (3/4 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
