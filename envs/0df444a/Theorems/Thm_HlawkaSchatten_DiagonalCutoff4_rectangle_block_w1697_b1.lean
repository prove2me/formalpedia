-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1697_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1697_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:41:27.262246+00:00
-- url     : https://prove2.me/theorems/566f9454-abd8-43c7-b539-0d8b7c91e588
-- title:
--   Hlawka rectangular localization block 2 on [5191/1024,5199/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1697_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66631/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3631/6250 : ℝ) else (10131/12500 : ℝ) ≤ X j i ∧ X j i ≤ (18047/20000 : ℝ) := by sorry
