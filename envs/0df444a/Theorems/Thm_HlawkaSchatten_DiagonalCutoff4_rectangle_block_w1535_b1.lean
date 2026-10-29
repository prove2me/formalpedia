-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1535_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:11:05.142095+00:00
-- url     : https://prove2.me/theorems/d7cfe121-aeb0-4cc6-872b-42aa84728a3b
-- title:
--   Hlawka rectangular localization block 2 on [4565/1024,4567/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by sorry
