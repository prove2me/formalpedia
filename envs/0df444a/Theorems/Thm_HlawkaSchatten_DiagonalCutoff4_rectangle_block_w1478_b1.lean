-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1478_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1478_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:48:43.818231+00:00
-- url     : https://prove2.me/theorems/6c0108b5-f09c-4e53-81fd-7611b6e5a372
-- title:
--   Hlawka rectangular localization block 2 on [4451/1024,4453/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1478_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by sorry
