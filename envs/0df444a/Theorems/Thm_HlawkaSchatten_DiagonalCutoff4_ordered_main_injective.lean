-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_main_injective
-- name    : HlawkaSchatten.DiagonalCutoff4.ordered_main_injective
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:33:40.883491+00:00
-- url     : https://prove2.me/theorems/04dc7c3f-a976-4a7e-b83d-86d49388251f
-- title:
--   Distinct dominant pair coordinates on the first cutoff-four interval
-- statement:
--   For $p\in[4,33/8]$, an ordered chart with the displayed normalized raw-frame parameters has pairwise distinct dominant pair coordinates. The signed coordinate orders need not satisfy any additional sign assumption.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.ordered_main_injective (p : ℝ) (hpa : (4:ℝ) ≤ p) (hpb : p ≤ (33/8:ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool)
    (hX : OrderedChart p (3667/2500:ℝ) (37167/20000:ℝ) (37991/50000:ℝ) X orders signs) :
    Function.Injective (fun i => orders i 0) := by sorry
