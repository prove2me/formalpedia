-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_09
-- name    : HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_09
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T14:03:16.940111+00:00
-- url     : https://prove2.me/theorems/fc278100-d571-41fc-b122-55eecaacbfe5
-- title:
--   Actual norm localization block [113/4,57/2]
-- statement:
--   For every real p in [113/4,57/2], coarse-box original norm data with singleton norm sum three, total norm below 591/500, and pair-gap sum below 2/((443/1000)p) imply the explicit norm cap and linear bounds of analytic domain 1. This block covers 4 consecutive certified slabs. Unequal singleton norms are allowed.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-4, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic contraction framework adapted from @bwdaugherty, Apache-2.0; notices retained.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_09 :
    ∀ p : ℝ, (113/4 : ℝ) ≤ p → p ≤ (57/2 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(1183/1000 : ℝ) ≤ X i i ∧ X i i ≤ -(477/1000 : ℝ)) →
      (∀ j i, j ≠ i → (3/4 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (591/500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((443/1000 : ℝ)*p) →
      (∀ j, -(2239/2000 : ℝ) ≤ X j j ∧ X j j ≤ -(4577/10000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1483/1250 : ℝ)) ∧
      (∀ j, lpNorm p (X j) ≤ (149298789/125000000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (82967765642843/51460500000000 : ℝ) ≤ X j i + X k i) ∧
      (59752599691237/10292100000000 : ℝ) ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by sorry
