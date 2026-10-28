-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1172_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:45:15.985779+00:00
-- url     : https://prove2.me/theorems/adab138d-71d1-4e98-8457-0ad23769dd45
-- title:
--   Hlawka rectangular localization block 3 on [2091/512,8365/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by sorry
