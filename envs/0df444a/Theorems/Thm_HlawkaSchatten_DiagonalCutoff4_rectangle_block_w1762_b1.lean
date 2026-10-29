-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1762_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1762_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:03:48.363982+00:00
-- url     : https://prove2.me/theorems/a4f310fe-3ca9-40d8-b0a3-b401f09df065
-- title:
--   Hlawka rectangular localization block 2 on [5951/1024,5967/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1762_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5951/1024 : ℝ) ≤ p) (hpb : p ≤ (5967/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (55586051/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1109/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1147/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17287/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58699/100000 : ℝ) else (20559/25000 : ℝ) ≤ X j i ∧ X j i ≤ (93117/100000 : ℝ) := by sorry
