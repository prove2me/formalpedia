-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factor_peeling_path
-- name    : LowRankUnivariateSOS.factor_peeling_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:26.723028+00:00
-- url     : https://prove2.me/theorems/36f53d7b-d6b5-51a5-a402-09180cf7a9e3
-- title:
--   Low Rank Univariate SOS: factor peeling path
-- statement:
--   The scalar peeling schedule induces a path of scaled pairs from the
--    original factorization `u = a·u₀` to the coprime target `g·u₀`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L204-L210
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L204-L210

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

theorem LowRankUnivariateSOS.factor_peeling_path
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      PeelingPath u u (scalePair g data.u0) := by sorry
