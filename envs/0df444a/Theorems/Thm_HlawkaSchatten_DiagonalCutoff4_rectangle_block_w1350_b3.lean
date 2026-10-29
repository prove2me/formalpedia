-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_block_w1350_b3
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:58:09.469691+00:00
-- url     : https://prove2.me/theorems/9969e307-7c02-4310-b9fb-fc5b53033acf
-- title:
--   Hlawka rectangular localization block 4 on [4309/1024,2155/512]
-- statement:
--   Under the normalized frame, sign and initial pair-tail bounds displayed formally, the displayed refined tail bounds or coordinate box hold throughout the stated exponent interval.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58957/100000 : ℝ) else (80001/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84383/100000 : ℝ) := by sorry
