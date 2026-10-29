-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1617_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:05:16.28383+00:00
-- url     : https://prove2.me/theorems/16b4cb98-dc28-4747-bb1a-6d743a010286
-- title:
--   Hlawka rectangular localization block 2 on [4783/1024,4787/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by sorry
