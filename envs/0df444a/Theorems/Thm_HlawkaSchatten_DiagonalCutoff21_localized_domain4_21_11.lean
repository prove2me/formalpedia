-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_11
-- name    : HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_11
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:44:17.732374+00:00
-- url     : https://prove2.me/theorems/51b65901-9fcf-4209-85fb-62390f0fe7aa
-- title:
--   Actual norm localization block [179/8,45/2]
-- statement:
--   For every real p in [179/8,45/2], coarse-box original norm data with singleton norm sum three, total norm below 3033/2500, and pair-gap sum below 2/((273/625)p) imply the explicit norm cap and linear bounds of analytic domain 0. This block covers 4 consecutive certified slabs. Unequal singleton norms are allowed.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-4, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic contraction framework adapted from @bwdaugherty, Apache-2.0; notices retained.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_11 :
    ∀ p : ℝ, (179/8 : ℝ) ≤ p → p ≤ (45/2 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ j, -(5559/5000 : ℝ) ≤ X j j ∧ X j j ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (11847/10000 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (1193402307/1000000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by sorry
