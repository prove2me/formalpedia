-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1690_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1690_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:38:55.720357+00:00
-- url     : https://prove2.me/theorems/f7231800-7dc0-4e7d-9db3-1f468d378fe9
-- title:
--   Hlawka rectangular localization block 2 on [5135/1024,5143/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1690_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5135/1024 : ℝ) ≤ p) (hpb : p ≤ (5143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37673239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8629/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66573/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5793/10000 : ℝ) else (16161/20000 : ℝ) ≤ X j i ∧ X j i ≤ (22533/25000 : ℝ) := by sorry
