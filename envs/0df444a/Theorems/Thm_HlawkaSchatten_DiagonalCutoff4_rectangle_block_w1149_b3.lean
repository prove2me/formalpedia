-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1149_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1149_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:34:27.8182+00:00
-- url     : https://prove2.me/theorems/7e9550dc-56ad-4427-b95f-eed93f8a264e
-- title:
--   Hlawka rectangular localization block 4 on [8341/2048,4171/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1149_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29922061/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7413/12500 : ℝ) else (7983/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4157/5000 : ℝ) := by sorry
