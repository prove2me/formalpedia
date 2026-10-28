-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1274_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:49:50.751642+00:00
-- url     : https://prove2.me/theorems/5fa22ef1-3385-467f-a0c8-b7496e9bb235
-- title:
--   Hlawka rectangular localization block 4 on [8467/2048,2117/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14851/25000 : ℝ) else (40103/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41709/50000 : ℝ) := by sorry
