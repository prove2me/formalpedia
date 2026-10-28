-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1317_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b1
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:30:44.637041+00:00
-- url     : https://prove2.me/theorems/5ebdbdc3-13d7-4dd8-b62d-a16ef07d5b42
-- title:
--   Hlawka rectangular localization block 2 on [1069/256,4277/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by sorry
