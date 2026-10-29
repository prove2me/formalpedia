-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1474_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:47:49.082122+00:00
-- url     : https://prove2.me/theorems/5ae83688-9bf5-416f-9cfa-38a8523061ac
-- title:
--   Hlawka rectangular localization block 3 on [4443/1024,4445/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3981/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1169/2000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (42877/50000 : ℝ) := by sorry
