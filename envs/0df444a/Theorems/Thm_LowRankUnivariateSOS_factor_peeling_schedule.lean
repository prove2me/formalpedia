-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factor_peeling_schedule
-- name    : LowRankUnivariateSOS.factor_peeling_schedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:23.604679+00:00
-- url     : https://prove2.me/theorems/d5f5c56e-b553-5959-9c90-be6fbb187923
-- title:
--   Low Rank Univariate SOS: factor peeling schedule
-- statement:
--   From the decomposition of the bad common factor into peelable pieces, we
--    obtain a full peeling schedule ending at some factor `g` that is coprime to
--    `σ(u₀)`. This is the formal counterpart of iteratively peeling the factors of
--    `h` in the proof of `\Cref{prop:second_order_property_factor}`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L190-L200
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L190-L200

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.factor_peeling_schedule
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      PeelingSchedule u data.u0 data.a g := by sorry
