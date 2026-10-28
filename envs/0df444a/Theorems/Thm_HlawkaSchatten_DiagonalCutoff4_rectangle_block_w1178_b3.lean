-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1178_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:47:42.232218+00:00
-- url     : https://prove2.me/theorems/738ec9c0-9268-42db-b2aa-5d927aafa07f
-- title:
--   Hlawka rectangular localization block 4 on [4185/1024,8371/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15559/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29663/50000 : ℝ) else (39959/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16641/20000 : ℝ) := by sorry
