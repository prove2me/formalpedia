-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4Private_real_three_w006
-- name    : HlawkaSchatten.DiagonalCutoff4Private.real_three_w006
-- status  : Open
-- author  : @anteater
-- created : 2026-10-28T03:33:39.004794+00:00
-- url     : https://prove2.me/theorems/ed7fc3cb-4321-4a92-9487-cf37c98f77eb
-- statement:
--   Private [4,6] window 6: 22/4 ≤ p ≤ 23/4.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . The cutoff-six theorem is proved: https://prove2.me/theorems/cc454546-564a-4781-a821-e78176963c44 . The extension to cutoff four is work in progress; the finite interval is not yet proved.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.DiagonalCutoff4Private

theorem real_three_w006 (p : ℝ) (hpa : (22/4 : ℝ) ≤ p) (hpb : p ≤ (23/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry

end HlawkaSchatten.DiagonalCutoff4Private
