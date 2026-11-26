-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_peelTerminalScale_ne_zero
-- name    : LowRankUnivariateSOS.peelTerminalScale_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:36.028626+00:00
-- url     : https://prove2.me/theorems/a423ac7d-995c-5305-b63e-02f2b864505b
-- title:
--   Low Rank Univariate SOS: peel Terminal Scale ne zero
-- statement:
--   The terminal scale never becomes zero if the initial coprime scale is
--    nonzero. This prevents the peeled target from degenerating during the
--    iteration.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L324-L332
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L324-L332

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.peelTerminalScale_ne_zero {gBase : Poly} {rs : List Poly}
    (hgBase : gBase ≠ 0) :
    peelTerminalScale gBase rs ≠ 0 := by sorry
