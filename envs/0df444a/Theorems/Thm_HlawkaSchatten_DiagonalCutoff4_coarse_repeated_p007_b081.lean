-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p007_b081
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p007_b081
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:26:56.18169+00:00
-- url     : https://prove2.me/theorems/0544b906-8d1d-4be3-887a-2789a1b39b7a
-- title:
--   Hlawka repeated profile 7, finite certificate block 82
-- statement:
--   For p in [39/8,5], the canonical charts whose indices lie in [243,246) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p007_b081 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 323) (hlo : 243 ≤ c.val) (hhi : c.val < 246)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
