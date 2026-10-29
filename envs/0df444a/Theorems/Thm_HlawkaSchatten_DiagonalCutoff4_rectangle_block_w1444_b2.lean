-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1444_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1444_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:37:44.243627+00:00
-- url     : https://prove2.me/theorems/20f9519f-0adc-4cb3-a2c9-0c85f6c07ce0
-- title:
--   Hlawka rectangular localization block 3 on [4403/1024,1101/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1444_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62909/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59143/100000 : ℝ) else (80531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84741/100000 : ℝ) := by sorry
