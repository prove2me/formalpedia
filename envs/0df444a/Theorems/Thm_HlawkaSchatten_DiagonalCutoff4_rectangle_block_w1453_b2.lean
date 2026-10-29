-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1453_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1453_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:39:28.401732+00:00
-- url     : https://prove2.me/theorems/10f13db2-b087-41c6-b618-20c3df8ee4d4
-- title:
--   Hlawka rectangular localization block 3 on [1103/256,4413/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1453_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12583/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29581/50000 : ℝ) else (4029/5000 : ℝ) ≤ X j i ∧ X j i ≤ (42387/50000 : ℝ) := by sorry
