-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1477_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1477_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:48:17.493871+00:00
-- url     : https://prove2.me/theorems/c8cee875-da4e-40d4-9e20-9e8e6c702a1c
-- title:
--   Hlawka rectangular localization block 2 on [4449/1024,4451/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1477_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by sorry
