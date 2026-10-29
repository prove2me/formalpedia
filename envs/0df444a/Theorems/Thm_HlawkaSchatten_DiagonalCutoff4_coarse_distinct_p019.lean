-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p019
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:32:50.668214+00:00
-- url     : https://prove2.me/theorems/5d1bebd7-2716-4b25-ad44-43d982348d14
-- title:
--   Hlawka distinct coordinate localization for 79/16 ≤ p ≤ 5
-- statement:
--   For p in [79/16,5], the displayed normalized parameters force positive pair coordinates after distinct-main and first-pair sign normalization, and bound all off-main pair ratios by two fifths.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) :
    (∀ X orders signs, OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by sorry
