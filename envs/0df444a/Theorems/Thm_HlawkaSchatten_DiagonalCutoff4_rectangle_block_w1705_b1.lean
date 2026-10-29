-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1705_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1705_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:44:48.184487+00:00
-- url     : https://prove2.me/theorems/b84e1c1e-4bf6-4abf-aaa5-7ec643f982c3
-- title:
--   Hlawka rectangular localization block 2 on [5255/1024,5263/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1705_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11657/20000 : ℝ) else (40659/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5647/6250 : ℝ) := by sorry
