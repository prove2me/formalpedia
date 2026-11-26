-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factor_peeling_decomposition
-- name    : LowRankUnivariateSOS.factor_peeling_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:50.037804+00:00
-- url     : https://prove2.me/theorems/43ca6c38-e54c-418a-b0e1-4c4a79c17981
-- title:
--   Low Rank Univariate SOS: factor peeling decomposition
-- statement:
--   This theorem extracts the factor data needed for the general-case proof.
--    Starting from the common factor `a` in `u = a·u₀`, it splits `a` into:
--    a base factor `gBase` coprime to `σ(u₀)`, and a list `rs` of factors dividing
--    `σ(u₀)` which must be peeled one by one. The terminal factor `g` is obtained by
--    replacing each peeled factor by `X²`, mirroring the passage from condition
--    (C3) in `\eqref{eq:prop_factored}`.
--
--    Proof sketch: factor `a` into irreducibles with `normalizedFactors`, partition
--    the factors into those dividing `σ(u₀)` and those that do not, define `gBase`
--    from the latter, and prove coprimality using the no-common-prime-factor
--    criterion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L82-L173
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean#L82-L173

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

theorem LowRankUnivariateSOS.factor_peeling_decomposition
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ gBase g : Poly, ∃ rs : List Poly,
      gBase ≠ 0 ∧
        data.a = gBase * rs.prod ∧
        g = peelTerminalScale gBase rs ∧
        IsCoprime g (sigma2 data.u0) ∧
        ∀ r ∈ rs, r ∣ sigma2 data.u0 := by sorry
