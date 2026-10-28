-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1285_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:52:00.924638+00:00
-- url     : https://prove2.me/theorems/a94ac98d-5c01-40f9-8f09-ad523fab57b1
-- title:
--   Hlawka rectangular localization block 3 on [1061/256,4245/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3677/6250 : ℝ) else (39807/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84127/100000 : ℝ) := by sorry
