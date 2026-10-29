-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1759_b0
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1759_b0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:02:03.589826+00:00
-- url     : https://prove2.me/theorems/919a1cf9-3563-4f55-8114-53a87581c4c8
-- title:
--   Hlawka rectangular localization block 1 on [5903/1024,5919/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1759_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i := by sorry
