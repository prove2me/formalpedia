-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1046_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:51:09.564642+00:00
-- url     : https://prove2.me/theorems/f0280bff-eb25-4ac7-b565-b554af01429a
-- title:
--   Hlawka rectangular localization block 4 on [4119/1024,8239/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29613/50000 : ℝ) else (79509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82907/100000 : ℝ) := by sorry
