-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1734_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1734_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:53:20.625671+00:00
-- url     : https://prove2.me/theorems/fdd77d36-d80b-48f9-b432-9e778d6956fe
-- title:
--   Hlawka rectangular localization block 2 on [5503/1024,5519/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1734_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5503/1024 : ℝ) ≤ p) (hpb : p ≤ (5519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (50897061/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3659/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4399/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8579/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(28653/50000 : ℝ) else (40291/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5787/6250 : ℝ) := by sorry
