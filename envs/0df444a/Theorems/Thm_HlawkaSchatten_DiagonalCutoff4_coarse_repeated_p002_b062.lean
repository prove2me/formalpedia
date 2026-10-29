-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p002_b062
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002_b062
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:18:34.695099+00:00
-- url     : https://prove2.me/theorems/8903179c-e503-41e4-b451-80f91b56d35b
-- title:
--   Hlawka repeated profile 2, finite certificate block 63
-- statement:
--   For p in [17/4,35/8], the canonical charts whose indices lie in [186,189) are excluded under the displayed normalized parameters.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p002_b062 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 323) (hlo : 186 ≤ c.val) (hhi : c.val < 189)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by sorry
