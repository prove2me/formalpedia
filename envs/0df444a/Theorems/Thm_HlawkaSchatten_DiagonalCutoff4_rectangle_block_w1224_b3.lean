-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1224_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:06:25.922666+00:00
-- url     : https://prove2.me/theorems/e77578a5-7b68-4c65-8d75-301633168d70
-- title:
--   Hlawka rectangular localization block 4 on [263/64,8417/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59363/100000 : ℝ) else (10007/12500 : ℝ) ≤ X j i ∧ X j i ≤ (41653/50000 : ℝ) := by sorry
