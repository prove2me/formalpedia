-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1440_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:36:41.174732+00:00
-- url     : https://prove2.me/theorems/99881f13-2604-47fd-be5e-bb9fd647a635
-- title:
--   Hlawka rectangular localization block 2 on [4399/1024,275/64]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by sorry
