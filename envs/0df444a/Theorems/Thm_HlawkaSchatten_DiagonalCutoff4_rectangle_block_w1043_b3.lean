-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1043_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:49:16.301335+00:00
-- url     : https://prove2.me/theorems/5ed9c4cf-4c3a-494c-9a5a-6777a8f0ef84
-- title:
--   Hlawka rectangular localization block 4 on [8235/2048,2059/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (159/200 : ℝ) ≤ X j i ∧ X j i ≤ (829/1000 : ℝ) := by sorry
