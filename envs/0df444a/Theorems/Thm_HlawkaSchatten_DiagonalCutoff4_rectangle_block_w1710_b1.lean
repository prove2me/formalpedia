-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1710_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:45:15.874271+00:00
-- url     : https://prove2.me/theorems/b86ef011-9a85-4874-afda-78ed1b0f024d
-- title:
--   Hlawka rectangular localization block 2 on [5295/1024,5303/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i := by sorry
