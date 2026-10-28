-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1225_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:07:23.946029+00:00
-- url     : https://prove2.me/theorems/005c313f-3d65-4247-a5a5-14251680acef
-- title:
--   Hlawka rectangular localization block 2 on [8417/2048,4209/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by sorry
