-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1062_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:04:18.695446+00:00
-- url     : https://prove2.me/theorems/822eb53b-6d2d-4d56-ba67-34cebc07025a
-- title:
--   Hlawka rectangular localization block 4 on [4127/1024,8255/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (1989/2500 : ℝ) ≤ X j i ∧ X j i ≤ (82943/100000 : ℝ) := by sorry
