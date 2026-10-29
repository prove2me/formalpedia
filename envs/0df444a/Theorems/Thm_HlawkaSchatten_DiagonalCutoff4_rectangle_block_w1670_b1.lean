-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1670_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1670_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:31:23.963574+00:00
-- url     : https://prove2.me/theorems/a9be0c7f-8c50-490f-8aad-130be8bb94f4
-- title:
--   Hlawka rectangular localization block 2 on [4995/1024,4999/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1670_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16227/100000 : ℝ)*pair X i i := by sorry
