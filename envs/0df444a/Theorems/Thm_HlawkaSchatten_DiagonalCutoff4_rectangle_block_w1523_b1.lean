-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1523_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1523_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:05:30.890347+00:00
-- url     : https://prove2.me/theorems/5c22c675-46ff-4a8c-b6f5-755eca532d4a
-- title:
--   Hlawka rectangular localization block 2 on [4541/1024,4543/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1523_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by sorry
