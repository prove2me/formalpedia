-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1039_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:45:39.262856+00:00
-- url     : https://prove2.me/theorems/138bfa31-bd43-48cc-a5d6-ce195db7e8d2
-- title:
--   Hlawka rectangular localization block 3 on [8231/2048,1029/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i := by sorry
