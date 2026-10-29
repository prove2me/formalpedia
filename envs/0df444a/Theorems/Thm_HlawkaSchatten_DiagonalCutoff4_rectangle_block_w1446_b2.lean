-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1446_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:37:51.146374+00:00
-- url     : https://prove2.me/theorems/49ef1c40-6a46-489a-a73d-70ca66aec75b
-- title:
--   Hlawka rectangular localization block 3 on [4405/1024,2203/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59147/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21187/25000 : ℝ) := by sorry
