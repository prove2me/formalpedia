-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain2_21_04_part0
-- name    : HlawkaSchatten.DiagonalCutoff21.localized_domain2_21_04_part0
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:59:01.807162+00:00
-- url     : https://prove2.me/theorems/38b343a0-a8f3-414b-b606-5511adfcbfda
-- title:
--   Actual norm localization subblock [43/2,345/16]
-- statement:
--   On [43/2,345/16], the original norm data in the displayed coarse box imply the same explicit analytic-domain bounds as the parent localization theorem. This proves 2 consecutive original parameter slabs; it is a faithful subinterval decomposition of that same localization result, with no new validity premise.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, Sections 3-4, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Generic contraction framework adapted from @bwdaugherty, Apache-2.0; notices retained.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.localized_domain2_21_04_part0 :
    ∀ p : ℝ, (43/2 : ℝ) ≤ p → p ≤ (345/16 : ℝ) → ∀ X : Fin 3 → Fin 3 → ℝ,
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
