-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1193_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:55:22.711414+00:00
-- url     : https://prove2.me/theorems/c9bbb535-4b77-4115-a8ed-2aafc60f528c
-- title:
--   Hlawka rectangular localization block 4 on [8385/2048,4193/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29669/50000 : ℝ) else (79963/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41619/50000 : ℝ) := by sorry
