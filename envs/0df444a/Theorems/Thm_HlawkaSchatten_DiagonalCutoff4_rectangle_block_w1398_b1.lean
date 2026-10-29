-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1398_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:29:24.007738+00:00
-- url     : https://prove2.me/theorems/5f0e409e-f128-4039-abb1-a7ba0e6d543e
-- title:
--   Hlawka rectangular localization block 2 on [4357/1024,2179/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by sorry
