-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1742_b1
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1742_b1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:56:33.662114+00:00
-- url     : https://prove2.me/theorems/e04cdc18-be04-437a-8cb9-77163229cebd
-- title:
--   Hlawka rectangular localization block 2 on [5631/1024,5647/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1742_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68767/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3607/6250 : ℝ) else (2534/3125 : ℝ) ≤ X j i ∧ X j i ≤ (23187/25000 : ℝ) := by sorry
