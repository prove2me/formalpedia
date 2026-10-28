-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1221_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:05:40.188997+00:00
-- url     : https://prove2.me/theorems/7eeec028-d5ae-4891-8d1d-2169674f19d3
-- title:
--   Hlawka rectangular localization block 4 on [8413/2048,4207/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(371/625 : ℝ) else (80047/100000 : ℝ) ≤ X j i ∧ X j i ≤ (833/1000 : ℝ) := by sorry
