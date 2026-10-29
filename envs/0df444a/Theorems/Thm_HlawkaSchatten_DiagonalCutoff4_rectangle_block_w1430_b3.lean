-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1430_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1430_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:35:23.550079+00:00
-- url     : https://prove2.me/theorems/2da1bf94-fec3-4f37-953d-7b57c9e1e839
-- title:
--   Hlawka rectangular localization block 4 on [4389/1024,2195/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1430_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4389/1024 : ℝ) ≤ p) (hpb : p ≤ (2195/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31641271/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(629/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(11823/20000 : ℝ) else (40227/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5293/6250 : ℝ) := by sorry
