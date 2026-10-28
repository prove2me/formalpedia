-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1145_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:33:00.93531+00:00
-- url     : https://prove2.me/theorems/e23bc9b9-ccfe-4317-ae71-ed305cff74b7
-- title:
--   Hlawka rectangular localization block 2 on [8337/2048,4169/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1145_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8337/2048 : ℝ) ≤ p) (hpb : p ≤ (4169/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29906449/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by sorry
