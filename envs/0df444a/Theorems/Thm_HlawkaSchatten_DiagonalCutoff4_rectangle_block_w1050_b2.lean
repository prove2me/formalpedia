-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1050_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:54:14.582514+00:00
-- url     : https://prove2.me/theorems/3433cc45-f611-480d-a91c-091e0c851f27
-- title:
--   Hlawka rectangular localization block 3 on [4121/1024,8243/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i := by sorry
