-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1721_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1721_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:49:48.107246+00:00
-- url     : https://prove2.me/theorems/c2eb1107-a132-4589-a233-b3ee53260adc
-- title:
--   Hlawka rectangular localization block 2 on [5383/1024,5391/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1721_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5383/1024 : ℝ) ≤ p) (hpb : p ≤ (5391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24825557/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8511/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58659/100000 : ℝ) else (81831/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90577/100000 : ℝ) := by sorry
