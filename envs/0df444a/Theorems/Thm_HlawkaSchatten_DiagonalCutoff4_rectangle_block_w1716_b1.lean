-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1716_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1716_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:47:22.450646+00:00
-- url     : https://prove2.me/theorems/2db6fbbc-d126-4dff-a054-68b494bb188e
-- title:
--   Hlawka rectangular localization block 2 on [5343/1024,5351/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1716_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16701/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58543/100000 : ℝ) else (40837/50000 : ℝ) ≤ X j i ∧ X j i ≤ (22627/25000 : ℝ) := by sorry
