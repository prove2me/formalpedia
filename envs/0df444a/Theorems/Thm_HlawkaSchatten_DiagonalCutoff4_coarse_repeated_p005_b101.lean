-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p005_b101
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p005_b101
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:58:54.753159+00:00
-- url     : https://prove2.me/theorems/77798fd3-e43e-48a3-9e57-473cbde8ff8a
-- title:
--   Hlawka repeated profile 5, finite certificate block 102
-- statement:
--   For p in [37/8,19/4], the canonical charts whose indices lie in [303,306) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p005_b101 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 323) (hlo : 303 ≤ c.val) (hhi : c.val < 306)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
