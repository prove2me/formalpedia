-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p004_b040
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p004_b040
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:15:18.785053+00:00
-- url     : https://prove2.me/theorems/db564b98-fa85-4f77-9261-e515a9968814
-- title:
--   Hlawka repeated profile 4, finite certificate block 41
-- statement:
--   For p in [9/2,37/8], the canonical charts whose indices lie in [120,123) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p004_b040 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 323) (hlo : 120 ≤ c.val) (hhi : c.val < 123)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
