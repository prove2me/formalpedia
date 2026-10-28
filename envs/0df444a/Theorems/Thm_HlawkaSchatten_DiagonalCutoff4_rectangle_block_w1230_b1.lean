-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1230_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:08:47.956379+00:00
-- url     : https://prove2.me/theorems/41a77d05-06ac-40de-8f32-5304af5887ea
-- title:
--   Hlawka rectangular localization block 2 on [4211/1024,8423/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by sorry
