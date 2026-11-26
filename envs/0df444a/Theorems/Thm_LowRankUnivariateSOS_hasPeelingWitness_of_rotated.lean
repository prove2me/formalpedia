-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_hasPeelingWitness_of_rotated
-- name    : LowRankUnivariateSOS.hasPeelingWitness_of_rotated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:35.903712+00:00
-- url     : https://prove2.me/theorems/dfb65b56-dfbe-480e-8293-563e73c3dd6e
-- title:
--   Low Rank Univariate SOS: has Peeling Witness of rotated
-- statement:
--   If rotated peeling data exist for every target in the next image, then we
--    get a full `HasPeelingWitness` statement. This is just packaging.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L233-L239
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L233-L239

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.hasPeelingWitness_of_rotated {u uImgPrev uImgNext : UPair}
    (hdata :
      ∀ q : Poly, InImageA uImgNext q → Nonempty (RotatedPeelingData u uImgPrev q)) :
    HasPeelingWitness u uImgPrev uImgNext := by sorry
