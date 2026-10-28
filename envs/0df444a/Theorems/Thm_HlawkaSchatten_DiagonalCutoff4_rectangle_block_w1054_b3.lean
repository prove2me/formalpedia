-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1054_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:57:39.886868+00:00
-- url     : https://prove2.me/theorems/1ef8d3b4-42f7-43ac-b60e-02399d184c2b
-- title:
--   Hlawka rectangular localization block 4 on [4123/1024,8247/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1851/3125 : ℝ) else (39767/50000 : ℝ) ≤ X j i ∧ X j i ≤ (3317/4000 : ℝ) := by sorry
