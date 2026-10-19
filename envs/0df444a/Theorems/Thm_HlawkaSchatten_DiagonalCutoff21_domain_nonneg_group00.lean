-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
-- name    : HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:01:50.642358+00:00
-- url     : https://prove2.me/theorems/b60ea380-c391-49fe-8496-6dfe8c4dee55
-- title:
--   Cyclic deficit nonnegative on norm-capped group 0
-- statement:
--   For every real p in [21,377/16], a real three-coordinate triple satisfying the displayed diagonal and off-diagonal coordinate intervals, actual singleton norm caps, actual total norm cap, linear complementary-pair coordinate floors and linear off-diagonal-sum floor has nonnegative original Hlawka deficit for the unchanged cyclic constant. No equality of singleton norms is assumed. Pointwise seven-norm Hessian estimates imply convexity on this invariant domain, and permutation averaging reduces the assertion to the defining cyclic supremum.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 5-7, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic norm/averaging framework by Ezzeri Esa, Apache-2.0; original notices retained.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 :
    ∀ p : ℝ, (21 : ℝ) ≤ p → p ≤ (377/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) →
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) →
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) →
      lpNorm p (X 0 + X 1 + X 2) ≤ (3033/2500 : ℝ) →
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) →
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 →
      0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
