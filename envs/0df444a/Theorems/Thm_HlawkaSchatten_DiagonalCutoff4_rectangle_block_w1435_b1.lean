-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1435_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1435_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:36:06.497419+00:00
-- url     : https://prove2.me/theorems/04e382c3-f236-4211-99ff-38c968fd273c
-- title:
--   Hlawka rectangular localization block 2 on [2197/512,4395/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1435_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by sorry
