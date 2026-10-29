-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:00:53.067681+00:00
-- url     : https://prove2.me/theorems/9c6e05a7-e810-42a8-bc26-36da7fdcb437
-- title:
--   Hlawka distinct coordinate localization for 135/32 ≤ p ≤ 17/4
-- statement:
--   For p in [135/32,17/4], the displayed normalized parameters force positive pair coordinates after distinct-main and first-pair sign normalization, and bound all off-main pair ratios by two fifths.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) :
    (∀ X orders signs, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by sorry
