-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1311_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b3
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:29:10.526639+00:00
-- url     : https://prove2.me/theorems/5c1e5bd2-d4fe-4fe5-9508-0c05936cbee3
-- title:
--   Hlawka rectangular localization block 4 on [2135/512,4271/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58881/100000 : ℝ) else (79771/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8423/10000 : ℝ) := by sorry
