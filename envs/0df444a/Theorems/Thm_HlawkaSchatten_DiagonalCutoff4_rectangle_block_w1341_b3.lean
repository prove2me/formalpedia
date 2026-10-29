-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1341_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:46:47.075833+00:00
-- url     : https://prove2.me/theorems/5d763bdb-b3a9-44fd-8577-263ca61e874f
-- title:
--   Hlawka rectangular localization block 4 on [1075/256,4301/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1341_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1075/256 : ℝ) ≤ p) (hpb : p ≤ (4301/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77344609/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (79949/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21087/25000 : ℝ) := by sorry
