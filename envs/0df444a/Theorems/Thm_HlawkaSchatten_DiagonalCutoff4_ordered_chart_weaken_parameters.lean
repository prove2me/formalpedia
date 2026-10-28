-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_chart_weaken_parameters
-- name    : HlawkaSchatten.DiagonalCutoff4.ordered_chart_weaken_parameters
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:48:11.83831+00:00
-- url     : https://prove2.me/theorems/5284b36d-5caf-47cb-9408-78b74baa66ad
-- title:
--   Weaken the parameters of an ordered Hlawka chart
-- statement:
--   For p at least one, decreasing the cyclic lower bound and the dominant-coordinate factor, and increasing the total norm cap, preserves an ordered normalized chart.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant .

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.ordered_chart_weaken_parameters {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by sorry
