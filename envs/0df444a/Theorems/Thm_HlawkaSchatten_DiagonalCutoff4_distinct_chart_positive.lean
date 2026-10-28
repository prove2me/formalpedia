-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_distinct_chart_positive
-- name    : HlawkaSchatten.DiagonalCutoff4.distinct_chart_positive
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:56:56.522978+00:00
-- url     : https://prove2.me/theorems/423b2ff2-4795-4c03-bf82-9d0d38de0e57
-- title:
--   Distinct Hlawka charts have positive pair coordinates after sign normalization
-- statement:
--   For $p\in[4,129/32]$, a normalized ordered chart whose main coordinates are 0, 1, 2 and whose first pair signs are all positive has all nine signs positive.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.distinct_chart_positive (p : ℝ) (hpa : (4:ℝ) ≤ p) (hpb : p ≤ (129/32:ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool)
    (hX : OrderedChart p (3667/2500:ℝ) (37167/20000:ℝ) (37991/50000:ℝ) X orders signs)
    (hfirst : ∀ h, signs 0 h=true) (hm : ∀ i, orders i 0=i) :
    signs=(fun _ _ => true) := by sorry
