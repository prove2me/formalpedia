-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1099_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1099_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:59:39.914928+00:00
-- url     : https://prove2.me/theorems/d7f591e1-c900-49ed-9f6a-795320178333
-- title:
--   Hlawka rectangular localization block 2 on [8291/2048,2073/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1099_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8317/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by sorry
