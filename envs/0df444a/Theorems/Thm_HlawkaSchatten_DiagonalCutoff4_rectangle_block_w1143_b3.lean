-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1143_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1143_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:31:33.195672+00:00
-- url     : https://prove2.me/theorems/508fbcc0-e7b5-4914-be64-c7684144ed2b
-- title:
--   Hlawka rectangular localization block 4 on [8335/2048,521/128]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1143_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59299/100000 : ℝ) else (79811/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83127/100000 : ℝ) := by sorry
