-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1501_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1501_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:02:34.937562+00:00
-- url     : https://prove2.me/theorems/cd2244bf-7ac4-4647-9a03-1b330b181ad4
-- title:
--   Hlawka rectangular localization block 3 on [4497/1024,4499/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1501_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2549/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(3661/6250 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (85931/100000 : ℝ) := by sorry
