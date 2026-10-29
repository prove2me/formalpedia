-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1429_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:35:23.051641+00:00
-- url     : https://prove2.me/theorems/e882e37e-35fc-42b4-be01-f3d589b4bcd8
-- title:
--   Hlawka rectangular localization block 3 on [1097/256,4389/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(629/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(59113/100000 : ℝ) else (2514/3125 : ℝ) ≤ X j i ∧ X j i ≤ (16937/20000 : ℝ) := by sorry
