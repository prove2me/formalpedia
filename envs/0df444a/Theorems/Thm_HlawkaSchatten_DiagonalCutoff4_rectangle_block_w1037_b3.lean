-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1037_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1037_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:44:07.784983+00:00
-- url     : https://prove2.me/theorems/e0b6541c-69cd-4aa0-9559-2a00eec6917a
-- title:
--   Hlawka rectangular localization block 4 on [8229/2048,4115/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1037_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (1987/2500 : ℝ) ≤ X j i ∧ X j i ≤ (41443/50000 : ℝ) := by sorry
