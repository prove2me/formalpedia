-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1758_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1758_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:01:33.382983+00:00
-- url     : https://prove2.me/theorems/26d9e06d-c974-4998-b11e-848f5dfef71a
-- title:
--   Hlawka rectangular localization block 2 on [5887/1024,5903/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1758_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17267/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11701/20000 : ℝ) else (82019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18609/20000 : ℝ) := by sorry
