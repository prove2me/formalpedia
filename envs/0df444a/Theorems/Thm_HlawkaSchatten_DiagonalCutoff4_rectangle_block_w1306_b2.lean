-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1306_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:27:13.762377+00:00
-- url     : https://prove2.me/theorems/6fe76624-49bf-46c8-89de-4d6b7d42584f
-- title:
--   Hlawka rectangular localization block 3 on [4265/1024,2133/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7359/12500 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84211/100000 : ℝ) := by sorry
