-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1637_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1637_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:17:01.493077+00:00
-- url     : https://prove2.me/theorems/769b7964-cee6-49d7-8aaf-f83dd2ef8802
-- title:
--   Hlawka rectangular localization block 2 on [4863/1024,4867/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1637_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13003/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29243/50000 : ℝ) else (20239/25000 : ℝ) ≤ X j i ∧ X j i ≤ (2753/3125 : ℝ) := by sorry
