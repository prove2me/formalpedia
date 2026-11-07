-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_zero
-- name    : LevyFoundations.leanlevy_chat16_exponent_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:39:34.963193+00:00
-- url     : https://prove2.me/theorems/0e2ea917-3011-4571-b234-d766efa208d9
-- title:
--   Levy-Khintchine exponent vanishes at zero
-- statement:
--   Every Levy-Khintchine exponent is normalised to vanish at frequency zero because each of its drift, Gaussian, and compensated-jump components vanishes there.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 5199-5202, exponent_zero.

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_compensatedIntegrand
open MeasureTheory

theorem LevyFoundations.leanlevy_chat16_exponent_zero
    (T : LevyFoundations.LevyKhintchineTriple) :
    LevyFoundations.exponent T 0 = 0 := by sorry
