-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1532_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1532_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:10:49.824381+00:00
-- url     : https://prove2.me/theorems/0cb21335-ec20-4cef-bbe2-d9988e6b6830
-- title:
--   Hlawka rectangular localization block 3 on [4559/1024,4561/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1532_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4559/1024 : ℝ) ≤ p) (hpb : p ≤ (4561/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82489471/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63767/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29361/50000 : ℝ) else (80531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86129/100000 : ℝ) := by sorry
