-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1421_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:33:37.396998+00:00
-- url     : https://prove2.me/theorems/22a9451a-a85d-4458-bf97-37dc3675d3df
-- title:
--   Hlawka rectangular localization block 3 on [1095/256,4381/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59097/100000 : ℝ) else (20101/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16931/20000 : ℝ) := by sorry
