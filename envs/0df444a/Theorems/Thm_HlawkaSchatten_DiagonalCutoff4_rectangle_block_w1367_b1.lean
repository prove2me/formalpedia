-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1367_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1367_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:09:00.78597+00:00
-- url     : https://prove2.me/theorems/262cd7e3-7c49-4e4c-987c-b8c3eb27a9fd
-- title:
--   Hlawka rectangular localization block 2 on [2163/512,4327/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1367_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by sorry
