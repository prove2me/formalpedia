-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p017
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:20:49.479744+00:00
-- url     : https://prove2.me/theorems/3ec4b8af-fc67-4d9d-9012-3b7aaa7c5dee
-- title:
--   Hlawka distinct coordinate localization for 77/16 ≤ p ≤ 39/8
-- statement:
--   For p in [77/16,39/8], the displayed normalized parameters force positive pair coordinates after distinct-main and first-pair sign normalization, and bound all off-main pair ratios by two fifths.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) :
    (∀ X orders signs, OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by sorry
