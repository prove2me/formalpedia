-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_certified_piece21_01
-- name    : HlawkaSchatten.DiagonalCutoff21.certified_piece21_01
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:07:18.103099+00:00
-- url     : https://prove2.me/theorems/977d1c8c-a399-47f5-9992-b4a087b22173
-- title:
--   Finite contraction certificate [85/4,43/2]
-- statement:
--   For all real p in [85/4,43/2], an original real triple satisfying the explicit coarse coordinate box, singleton norm sum three, total norm bound 3033/2500, and original pair-gap bound has nonnegative original cyclic-constant deficit. This piece covers 8 consecutive parameter slabs. Root bounds, budgets, all ten contraction rounds and the linear pair/offsum floors are proved here; the shared norm-domain nonnegativity theorem is imported. Unequal singleton norms are allowed.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-7, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Contraction framework adapted from @bwdaugherty, Apache-2.0; source notices retained.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.certified_piece21_01 :
    ∀ p : ℝ, (85/4 : ℝ) ≤ p → p ≤ (43/2 : ℝ) →
    ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
