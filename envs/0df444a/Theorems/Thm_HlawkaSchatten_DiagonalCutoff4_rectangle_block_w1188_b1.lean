-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1188_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:49:59.205424+00:00
-- url     : https://prove2.me/theorems/42c30e00-1e89-45a9-ab0e-fac952cf3e12
-- title:
--   Hlawka rectangular localization block 2 on [2095/512,8381/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by sorry
