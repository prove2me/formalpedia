-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1610_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:04:02.032374+00:00
-- url     : https://prove2.me/theorems/c5a1beb4-0993-4d23-87ed-d1150e1f406e
-- title:
--   Hlawka rectangular localization block 2 on [4755/1024,4759/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by sorry
