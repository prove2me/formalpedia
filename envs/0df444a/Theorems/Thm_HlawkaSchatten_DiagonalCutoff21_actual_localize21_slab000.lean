-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_actual_localize21_slab000
-- name    : HlawkaSchatten.DiagonalCutoff21.actual_localize21_slab000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:25:29.570982+00:00
-- url     : https://prove2.me/theorems/231c7c8c-51db-449c-9622-f7504a57a428
-- title:
--   Actual norm localization on [21,673/32]
-- statement:
--   For every real p in [21,673/32], a coarse-box triple with original singleton norm sum three, total norm below 3033/2500, and original pair-gap sum below 2/((273/625)p) obeys the displayed actual singleton norm cap, contracted coordinate box, linear complementary-pair floors and strict off-diagonal-sum floor. Singleton norms need not be equal. This is the actual-norm localization certificate for one parameter slab, with no imported theorem dependencies and no abstract validity predicate.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-4, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic contraction framework adapted from @bwdaugherty, Apache-2.0, with original notices retained.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.actual_localize21_slab000 :
    ∀ p : ℝ, (21 : ℝ) ≤ p → p ≤ (673/32 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
      (∀ i, -(607/500 : ℝ) ≤ X i i ∧ X i i ≤ -(189/500 : ℝ)) →
      (∀ j i, j ≠ i → (349/500 : ℝ) ≤ X j i ∧ X j i ≤ (607/500 : ℝ)) →
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 →
      lpNorm p (X 0 + X 1 + X 2) < (3033/2500 : ℝ) →
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((273/625 : ℝ)*p) →
      (∀ i, lpNorm p (X i) ≤ (596197839/500000000 : ℝ)) ∧
      (∀ i, -(689/625 : ℝ) ≤ X i i ∧ X i i ≤ -(881/2000 : ℝ)) ∧
      (∀ j i, j ≠ i → (3779/5000 : ℝ) ≤ X j i ∧ X j i ≤ (1183/1000 : ℝ)) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → (1139124440087/716625000000 : ℝ) ≤ X j i + X k i) ∧
      (3314799982801/573300000000 : ℝ) < X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by sorry
