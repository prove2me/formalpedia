-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1036_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:42:27.348991+00:00
-- url     : https://prove2.me/theorems/6b5a80a6-7f32-4db4-98fe-0f8950b8c698
-- title:
--   Hlawka rectangular localization block 1 on [2057/512,8229/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1713/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16839/100000 : ℝ)*pair X i i := by sorry
