-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1066_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:06:44.112985+00:00
-- url     : https://prove2.me/theorems/4b2055f5-38d3-4792-ae4f-e8eac2b76279
-- title:
--   Hlawka rectangular localization block 2 on [4129/1024,8259/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by sorry
