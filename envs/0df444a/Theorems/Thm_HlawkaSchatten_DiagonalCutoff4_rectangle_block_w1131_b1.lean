-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1131_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:26:11.008998+00:00
-- url     : https://prove2.me/theorems/bf2b4b13-c0f6-4bd5-9275-3aa8751f93e4
-- title:
--   Hlawka rectangular localization block 2 on [8323/2048,2081/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by sorry
