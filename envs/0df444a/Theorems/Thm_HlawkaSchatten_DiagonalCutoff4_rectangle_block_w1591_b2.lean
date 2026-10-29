-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1591_b2
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1591_b2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:54:42.940178+00:00
-- url     : https://prove2.me/theorems/17b71e90-7fba-4e23-9b50-7a6a8e795b4e
-- title:
--   Hlawka rectangular localization block 3 on [4679/1024,4683/1024]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1591_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14497/25000 : ℝ) else (16009/20000 : ℝ) ≤ X j i ∧ X j i ≤ (87627/100000 : ℝ) := by sorry
