-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p002_b022
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b022
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:13:16.441969+00:00
-- url     : https://prove2.me/theorems/2f888d22-cfeb-4f80-8ad2-7eafa7b58ede
-- title:
--   Hlawka distinct profile 2, finite certificate block 23
-- statement:
--   For p in [65/16,131/32], the canonical charts whose indices lie in [44,46) are excluded under the displayed normalized parameters. The two positive indices 63 and 87 are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b022 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 44 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
