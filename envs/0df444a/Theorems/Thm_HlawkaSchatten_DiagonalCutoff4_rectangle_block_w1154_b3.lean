-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1154_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1154_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:36:34.815529+00:00
-- url     : https://prove2.me/theorems/037a9fad-1fd1-441c-8888-45369bac985c
-- title:
--   Hlawka rectangular localization block 4 on [4173/1024,8347/2048]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1154_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(14827/25000 : ℝ) else (15969/20000 : ℝ) ≤ X j i ∧ X j i ≤ (83151/100000 : ℝ) := by sorry
