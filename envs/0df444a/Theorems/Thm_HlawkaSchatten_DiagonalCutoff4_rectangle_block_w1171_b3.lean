-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1171_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:44:43.713356+00:00
-- url     : https://prove2.me/theorems/56b3a786-09a7-4026-8cb8-efc6f86c6a0d
-- title:
--   Hlawka rectangular localization block 4 on [8363/2048,2091/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59321/100000 : ℝ) else (9987/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83189/100000 : ℝ) := by sorry
