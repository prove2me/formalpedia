-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1040_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:46:17.447155+00:00
-- url     : https://prove2.me/theorems/6f31fe1e-3caf-4a9f-a6a3-923502ad7f3f
-- title:
--   Hlawka rectangular localization block 4 on [1029/256,8233/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (7949/10000 : ℝ) ≤ X j i ∧ X j i ≤ (82893/100000 : ℝ) := by sorry
