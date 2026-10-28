-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1065_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:06:39.875815+00:00
-- url     : https://prove2.me/theorems/d6cab19a-844b-4d08-8d4e-ec7a987d2905
-- title:
--   Hlawka rectangular localization block 4 on [8257/2048,4129/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1481/2500 : ℝ) else (79569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1659/2000 : ℝ) := by sorry
