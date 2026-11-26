-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_PeelingSchedule_toPath
-- name    : LowRankUnivariateSOS.PeelingSchedule.toPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:28.664262+00:00
-- url     : https://prove2.me/theorems/9ecd9e5c-06fa-598b-a551-8ab8a281c2c4
-- title:
--   Peeling Schedule: to Path
-- statement:
--   Every peeling schedule induces a path of scaled pairs. This simply turns
--    the scalar recursion into the pair-valued recursion used by the orthogonality
--    lemmas.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L311-L319
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L311-L319

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.PeelingSchedule.toPath {u u0 : UPair} {gStart gEnd : Poly}
    (hsched : PeelingSchedule u u0 gStart gEnd) :
    PeelingPath u (scalePair gStart u0) (scalePair gEnd u0) := by sorry
