-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1454_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:39:29.176314+00:00
-- url     : https://prove2.me/theorems/4fa5b369-23a1-4863-88a3-cdacbdf3fc69
-- title:
--   Hlawka rectangular localization block 2 on [4413/1024,2207/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1454_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4413/1024 : ℝ) ≤ p) (hpb : p ≤ (2207/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79579139/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7863/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by sorry
