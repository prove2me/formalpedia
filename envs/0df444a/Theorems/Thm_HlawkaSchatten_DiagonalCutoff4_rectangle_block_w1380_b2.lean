-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1380_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:13:10.660831+00:00
-- url     : https://prove2.me/theorems/b3d0d859-33fd-40fc-9c90-fdd277835e82
-- title:
--   Hlawka rectangular localization block 3 on [4339/1024,1085/256]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7859/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7377/12500 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84499/100000 : ℝ) := by sorry
