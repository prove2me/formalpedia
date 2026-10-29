-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1522_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1522_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:05:29.998085+00:00
-- url     : https://prove2.me/theorems/dae86415-b855-4b8c-ab5e-5ba8df251fb8
-- title:
--   Hlawka rectangular localization block 3 on [4539/1024,4541/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1522_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63753/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2347/4000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43033/50000 : ℝ) := by sorry
