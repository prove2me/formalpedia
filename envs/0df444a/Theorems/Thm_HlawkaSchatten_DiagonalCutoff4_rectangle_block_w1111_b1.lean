-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1111_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:04:14.037302+00:00
-- url     : https://prove2.me/theorems/fd90ebae-b036-40d8-aebc-3e742e2b2a0d
-- title:
--   Hlawka rectangular localization block 2 on [8303/2048,519/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by sorry
