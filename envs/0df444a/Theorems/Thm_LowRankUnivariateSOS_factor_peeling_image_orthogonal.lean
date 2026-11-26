-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factor_peeling_image_orthogonal
-- name    : LowRankUnivariateSOS.factor_peeling_image_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:28.352296+00:00
-- url     : https://prove2.me/theorems/f4de0399-554d-5583-8bee-88233cee3974
-- title:
--   Low Rank Univariate SOS: factor peeling image orthogonal
-- statement:
--   This is the formal output of the whole peeling construction. At any SOCP,
--    after peeling all bad factors we obtain a nonzero `g` coprime to `σ(u₀)` such
--    that the residual is orthogonal to `im(A_{g u₀})`. This is exactly the
--    transformed-image orthogonality promised by the paper's general-case argument
--    around `\Cref{prop:second_order_property_factor}`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L221-L233
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L221-L233

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
variable {B : DotForm}

theorem LowRankUnivariateSOS.factor_peeling_image_orthogonal
    (p : Poly) (u : UPair)
    (hsocp : IsSOCP B p u)
    (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      ImageOrthogonalResidual B p (scalePair data.a data.u0) (scalePair g data.u0) := by sorry
