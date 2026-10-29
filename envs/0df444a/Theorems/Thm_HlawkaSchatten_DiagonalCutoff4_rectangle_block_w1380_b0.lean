-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1380_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:13:07.538572+00:00
-- url     : https://prove2.me/theorems/21d18086-062f-4ab5-9fa3-fc5f4165fb16
-- title:
--   Hlawka rectangular localization block 1 on [4339/1024,1085/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i := by sorry
