-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1305_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1305_b3
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:27:13.345681+00:00
-- url     : https://prove2.me/theorems/f1cd3dcc-d914-4bae-b2f5-6f5caec367f8
-- title:
--   Hlawka rectangular localization block 4 on [533/128,4265/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1305_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5887/10000 : ℝ) else (15947/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42103/50000 : ℝ) := by sorry
