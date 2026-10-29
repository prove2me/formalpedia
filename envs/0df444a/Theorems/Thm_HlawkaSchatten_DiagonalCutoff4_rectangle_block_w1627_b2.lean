-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1627_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:10:12.223014+00:00
-- url     : https://prove2.me/theorems/7c68df66-0ef6-453a-abf3-aa8da57ca209
-- title:
--   Hlawka rectangular localization block 3 on [4823/1024,4827/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64977/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29189/50000 : ℝ) else (80767/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87997/100000 : ℝ) := by sorry
