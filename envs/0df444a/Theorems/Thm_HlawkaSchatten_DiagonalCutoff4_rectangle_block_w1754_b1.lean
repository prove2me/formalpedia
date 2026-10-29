-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1754_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1754_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:01:19.301999+00:00
-- url     : https://prove2.me/theorems/386d6086-61c4-48b6-8b7a-e08d554b694c
-- title:
--   Hlawka rectangular localization block 2 on [5823/1024,5839/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1754_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68989/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (20449/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92973/100000 : ℝ) := by sorry
