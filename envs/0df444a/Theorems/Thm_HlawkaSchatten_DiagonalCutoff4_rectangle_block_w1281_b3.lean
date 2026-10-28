-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1281_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:51:06.185689+00:00
-- url     : https://prove2.me/theorems/f7edd026-9f56-42bd-8348-0829e2540c1d
-- title:
--   Hlawka rectangular localization block 4 on [265/64,4241/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7353/12500 : ℝ) else (7959/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84111/100000 : ℝ) := by sorry
