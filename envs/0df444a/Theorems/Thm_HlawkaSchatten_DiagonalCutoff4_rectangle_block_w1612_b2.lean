-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1612_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1612_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:04:34.428678+00:00
-- url     : https://prove2.me/theorems/a2fd103e-144e-4ca8-a695-2a5f41307d68
-- title:
--   Hlawka rectangular localization block 3 on [4763/1024,4767/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1612_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16337/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32463/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7277/12500 : ℝ) else (40237/50000 : ℝ) ≤ X j i ∧ X j i ≤ (17569/20000 : ℝ) := by sorry
