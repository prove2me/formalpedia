-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1382_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:13:25.153404+00:00
-- url     : https://prove2.me/theorems/dd4eb678-4bd0-4809-a6ea-6dbfa5e805ab
-- title:
--   Hlawka rectangular localization block 3 on [4341/1024,2171/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62873/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2951/5000 : ℝ) else (16037/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84507/100000 : ℝ) := by sorry
