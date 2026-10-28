-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1127_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:11:13.532076+00:00
-- url     : https://prove2.me/theorems/00a8546a-c53e-48ba-8dcb-a4725cbb1c3e
-- title:
--   Hlawka rectangular localization block 3 on [8319/2048,65/16]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by sorry
