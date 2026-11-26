-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_rotatedPeelingData_of_factor_step
-- name    : LowRankUnivariateSOS.rotatedPeelingData_of_factor_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:31.744159+00:00
-- url     : https://prove2.me/theorems/33ff3afa-6fe0-48c6-9be7-c0e21b15eaf4
-- title:
--   Low Rank Univariate SOS: rotated Peeling Data of factor step
-- statement:
--   One algebraic factor step `gStart -> gNext` produces the rotated data
--    needed for the analytic peeling argument. This is where divisibility of the
--    peeled factor by `σ(u₀)` is converted into the statement that the quadratic
--    term already lies in the previous image.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L195-L229
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L195-L229

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.rotatedPeelingData_of_factor_step {u u0 : UPair} {a gStart gNext : Poly}
    (hu : u = scalePair a u0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hfg : QuadraticFactorStep u0 gStart gNext)
    (q : Poly) (hq : InImageA (scalePair gNext u0) q) :
    Nonempty (RotatedPeelingData u (scalePair gStart u0) q) := by sorry
