-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1228_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:07:51.881964+00:00
-- url     : https://prove2.me/theorems/fd2853d6-a74d-4c75-8158-718ed33cb991
-- title:
--   Hlawka rectangular localization block 4 on [2105/512,8421/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29683/50000 : ℝ) else (80067/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16663/20000 : ℝ) := by sorry
