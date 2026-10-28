-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_chart_ratio_of_cases
-- name    : HlawkaSchatten.DiagonalCutoff4.positive_chart_ratio_of_cases
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:38:59.014776+00:00
-- url     : https://prove2.me/theorems/901328e3-72f1-493e-8f6f-d649c270d562
-- title:
--   Uniform positive-chart tail ratio from the two canonical positive cases
-- statement:
--   For arbitrary real parameters p, k, A and d, suppose the two canonical positive ordered charts have pair-tail ratios at most two fifths. Then every positive ordered chart with main coordinates 0, 1, 2 has the same bounds.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.positive_chart_ratio_of_cases (p k A d : ℝ)
    (hpositive : ∀ c : Fin 88, c=63 ∨ c=87 → ∀ X : Fin 3 → Fin 3 → ℝ,
      OrderedChart p k A d X (distinctOrders c) (fun _ _ => true) →
      ∀ i h, i ≠ h → |pair X i h| ≤ (2/5:ℝ)*pair X i i)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (hX : OrderedChart p k A d X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (2/5:ℝ)*pair X i i := by sorry
