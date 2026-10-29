-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1421_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:35.707918+00:00
-- url     : https://prove2.me/theorems/5bbe1de1-957b-4a5c-b2a6-291317d1edb9
-- title:
--   Hlawka rectangular localization block 2 on [1095/256,4381/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (633/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by sorry
