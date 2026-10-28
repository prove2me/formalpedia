-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1173_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:45:32.39264+00:00
-- url     : https://prove2.me/theorems/c4ebf71f-47e4-488f-a479-0777021c7211
-- title:
--   Hlawka rectangular localization block 4 on [8365/2048,4183/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1173_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8365/2048 : ℝ) ≤ p) (hpb : p ≤ (4183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30015783/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59323/100000 : ℝ) else (79903/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41597/50000 : ℝ) := by sorry
