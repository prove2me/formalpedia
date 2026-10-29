-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1368_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:09:08.149513+00:00
-- url     : https://prove2.me/theorems/48c1509b-ea8b-46d6-a27c-024b5f50f77c
-- title:
--   Hlawka rectangular localization block 3 on [4327/1024,541/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3687/6250 : ℝ) else (16021/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84453/100000 : ℝ) := by sorry
