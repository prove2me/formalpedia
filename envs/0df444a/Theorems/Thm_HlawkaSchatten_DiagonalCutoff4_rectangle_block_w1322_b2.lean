-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1322_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b2
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:31:35.01596+00:00
-- url     : https://prove2.me/theorems/f3300596-3dca-40a4-afdc-184c72293d53
-- title:
--   Hlawka rectangular localization block 3 on [4281/1024,2141/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(29451/50000 : ℝ) else (79837/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42137/50000 : ℝ) := by sorry
