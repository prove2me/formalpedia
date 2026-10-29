-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1447_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:38:02.042614+00:00
-- url     : https://prove2.me/theorems/41d49f74-3a3d-4c15-a6e9-3f4f0c69150c
-- title:
--   Hlawka rectangular localization block 3 on [2203/512,4407/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62911/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59149/100000 : ℝ) else (80547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5297/6250 : ℝ) := by sorry
