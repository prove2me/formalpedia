-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_distinct_sign_s38
-- name    : HlawkaSchatten.DiagonalCutoff4.distinct_sign_s38
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:54:27.614097+00:00
-- url     : https://prove2.me/theorems/59cd34ec-6400-43b2-9f19-0b96ef49febd
-- title:
--   Hlawka distinct-coordinate sign pattern 39 excluded
-- statement:
--   For exponents in $[4,129/32]$, no ordered chart with the displayed parameters and sign matrix has dominant coordinates 0, 1, 2. All eight choices of tail orders are covered.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.distinct_sign_s38 (p : ℝ) (hpa : (4:ℝ) ≤ p) (hpb : p ≤ (129/32:ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (hX : OrderedChart p (3667/2500:ℝ) (37167/20000:ℝ) (37991/50000:ℝ) X orders ![![true, true, true], ![true, false, false], ![true, true, false]])
    (hm0 : orders 0 0=0) (hm1 : orders 1 0=1) (hm2 : orders 2 0=2) : False := by sorry
