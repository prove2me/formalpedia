-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1094_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:58:02.475848+00:00
-- url     : https://prove2.me/theorems/d5699bbe-e6ae-4ac9-8d82-6037f5b1bfba
-- title:
--   Hlawka rectangular localization block 4 on [4143/1024,8287/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29631/50000 : ℝ) else (3983/5000 : ℝ) ≤ X j i ∧ X j i ≤ (10377/12500 : ℝ) := by sorry
