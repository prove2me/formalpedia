-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1119_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:07:30.862732+00:00
-- url     : https://prove2.me/theorems/3c9e0223-ae08-475e-b87b-297880ac22f3
-- title:
--   Hlawka rectangular localization block 4 on [8311/2048,1039/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59281/100000 : ℝ) else (79737/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83073/100000 : ℝ) := by sorry
