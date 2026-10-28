-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_chart_ratio
-- name    : HlawkaSchatten.DiagonalCutoff4.positive_chart_ratio
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:56:57.737984+00:00
-- url     : https://prove2.me/theorems/cc9ea842-7373-452f-90ac-6c5b1c0af991
-- title:
--   Hlawka positive ordered charts have tail ratio at most two fifths
-- statement:
--   With the displayed normalized parameters and distinct main coordinates 0, 1, 2, every pair tail has relative absolute value at most $2/5$, for $p\in[4,33/8]$.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.positive_chart_ratio (p : ℝ) (hpa : (4:ℝ) ≤ p) (hpb : p ≤ (33/8:ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (hX : OrderedChart p (3667/2500:ℝ) (37167/20000:ℝ) (37991/50000:ℝ) X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (2/5:ℝ)*pair X i i := by sorry
