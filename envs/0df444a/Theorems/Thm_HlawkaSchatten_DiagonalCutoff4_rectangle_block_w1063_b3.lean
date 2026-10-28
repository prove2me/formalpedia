-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1063_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:04:36.205714+00:00
-- url     : https://prove2.me/theorems/96a8208c-5b4e-4443-bccd-2eb9dda2c1dd
-- title:
--   Hlawka rectangular localization block 4 on [8255/2048,129/32]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (79563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41473/50000 : ℝ) := by sorry
