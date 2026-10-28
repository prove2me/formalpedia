-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1235_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:10:51.075775+00:00
-- url     : https://prove2.me/theorems/eec908ee-ecbb-4205-be64-8929e0fea129
-- title:
--   Hlawka rectangular localization block 2 on [8427/2048,2107/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by sorry
