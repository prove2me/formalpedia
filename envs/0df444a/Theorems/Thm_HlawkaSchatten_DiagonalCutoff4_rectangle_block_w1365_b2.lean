-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1365_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:08:52.747706+00:00
-- url     : https://prove2.me/theorems/93f5dbe3-a94c-455e-bcd2-ee3c5b98c4a5
-- title:
--   Hlawka rectangular localization block 3 on [1081/256,4325/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29493/50000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84441/100000 : ℝ) := by sorry
