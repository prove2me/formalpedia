-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1582_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:50:23.796763+00:00
-- url     : https://prove2.me/theorems/17b10a2b-48b2-4532-8c51-24e3aa7ff71a
-- title:
--   Hlawka rectangular localization block 3 on [4659/1024,4661/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1277/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(737/1250 : ℝ) else (81039/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2161/2500 : ℝ) := by sorry
