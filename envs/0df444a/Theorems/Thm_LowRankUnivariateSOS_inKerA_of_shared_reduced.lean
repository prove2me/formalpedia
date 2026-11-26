-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_inKerA_of_shared_reduced
-- name    : LowRankUnivariateSOS.inKerA_of_shared_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:45.07352+00:00
-- url     : https://prove2.me/theorems/96c7bd15-f775-45a4-9bb5-3e193dec86e2
-- title:
--   Low Rank Univariate SOS: in Ker A of shared reduced
-- statement:
--   If a vector is killed by `A_{g u₀}` with `g ≠ 0`, then it is already killed
--    by `A_{a u₀}` for any other scale `a`. This is the formal reason that kernel
--    cone terms produced in the reduced `h = 1` model can be reused for the
--    original factorization.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L13-L19
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L13-L19

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.inKerA_of_shared_reduced {a g : Poly} {u0 w : UPair}
    (hg : g ≠ 0) (hker : InKerA (scalePair g u0) w) :
    InKerA (scalePair a u0) w := by sorry
