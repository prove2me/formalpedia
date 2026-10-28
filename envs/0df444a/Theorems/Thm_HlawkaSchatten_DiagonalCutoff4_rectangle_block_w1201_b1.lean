-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1201_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1201_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:58:29.585278+00:00
-- url     : https://prove2.me/theorems/e6633409-1a7e-4dd4-a33c-4a1932a7cc82
-- title:
--   Hlawka rectangular localization block 2 on [8393/2048,4197/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1201_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by sorry
