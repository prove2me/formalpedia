-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_peelingSchedule_of_factors
-- name    : LowRankUnivariateSOS.peelingSchedule_of_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:12.890171+00:00
-- url     : https://prove2.me/theorems/f8e4db71-7bba-410f-8c7f-40d30a1237ec
-- title:
--   Low Rank Univariate SOS: peeling Schedule of factors
-- statement:
--   A list of peeled factors, together with a local theorem for each factor,
--    builds the full recursive peeling schedule. This is the formal implementation
--    of the paper's instruction to peel the factors of `h` one at a time.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L337-L368
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L337-L368

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.peelingSchedule_of_factors {u u0 : UPair} {gBase : Poly} {rs : List Poly}
    (hrs : ∀ r ∈ rs, r ∣ sigma2 u0)
    (hstep :
      ∀ {gStart gNext : Poly}, QuadraticFactorStep u0 gStart gNext →
        HasPeelingWitness u (scalePair gStart u0) (scalePair gNext u0)) :
    PeelingSchedule u u0 (gBase * rs.prod) (peelTerminalScale gBase rs) := by sorry
