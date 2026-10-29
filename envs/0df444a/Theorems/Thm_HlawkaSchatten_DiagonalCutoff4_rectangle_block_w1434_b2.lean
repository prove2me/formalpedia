-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1434_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1434_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:36:03.522091+00:00
-- url     : https://prove2.me/theorems/55fd5d3d-ae6c-4aef-94f4-3551fa1cdcaa
-- title:
--   Hlawka rectangular localization block 3 on [4393/1024,2197/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1434_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59123/100000 : ℝ) else (20119/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84703/100000 : ℝ) := by sorry
