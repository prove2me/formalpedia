-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1771_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1771_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:06:39.732553+00:00
-- url     : https://prove2.me/theorems/84ff08f6-5a41-4c97-b509-3ac2d369a453
-- title:
--   Hlawka rectangular localization block 2 on [6095/1024,6111/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1771_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8667/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(5913/10000 : ℝ) else (5169/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93273/100000 : ℝ) := by sorry
