-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1443
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_w1443
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:37:30.024428+00:00
-- url     : https://prove2.me/theorems/e29d792b-0808-4e81-a813-061e8903b186
-- title:
--   Sharp diagonal Hlawka inequality in real dimension three for 2201/512 ≤ p ≤ 4403/1024
-- statement:
--   For every real p in [2201/512,4403/1024], the campaign cyclic constant satisfies the Hlawka inequality for every triple in real dimension three. No sign or localization assumption is imposed.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten

theorem HlawkaSchatten.DiagonalCutoff4.real_three_w1443 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
