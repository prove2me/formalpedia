-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_normalized_positive_first
-- name    : HlawkaSchatten.DiagonalCutoff4.normalized_positive_first
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:03:51.967343+00:00
-- url     : https://prove2.me/theorems/e2a20870-8c57-4e87-8fc4-79fc530361a4
-- title:
--   Normalize every counterexample on the first cutoff-four interval into a positive chart
-- statement:
--   For $4≤p≤129/32$, the displayed cyclic-constant and envelope bounds imply that any strict real three-dimensional counterexample has a normalized frame with all pair tails nonnegative and their ratios at most $2/5$. The fine lower bound k is retained in the frame.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.normalized_positive_first {p k : ℝ} (hpa : 4 ≤ p) (hpb : p ≤ (129/32:ℝ))
    (hk : (3667/2500:ℝ) ≤ k) (hlinear : k < cyclicConstant p)
    (henvelope : scalarEnvelope p (12389/20000:ℝ) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ Y : Fin 3 → Fin 3 → ℝ,
      Frame p k (37167/20000:ℝ) (37991/50000:ℝ) Y ∧
      (∀ i h, i ≠ h → 0 ≤ pair Y i h) ∧
      (∀ i h, i ≠ h → |pair Y i h| ≤ (2/5:ℝ)*pair Y i i) ∧
      tripleDeficit p (cyclicConstant p) Y < 0 := by sorry
