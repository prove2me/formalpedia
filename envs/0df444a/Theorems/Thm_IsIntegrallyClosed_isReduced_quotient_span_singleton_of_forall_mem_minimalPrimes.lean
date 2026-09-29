-- Prove2me | Theorems.Thm_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
-- name    : IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/1f46f548-3cff-5c39-bb01-abdeb4776c73
-- title:
--   Reducedness of A/(x) for normal domains via minimal primes
-- statement:
--   Let $A$ be a commutative ring that is a Noetherian integral domain and is integrally closed in its field of fractions, and let $x \in A$ be non-zero. Assume that for every prime ideal $P$ of $A$ belonging to the minimal primes of the principal ideal $\operatorname{span}\{x\}$ — that is, $P$ is minimal among the primes containing $(x)$ — the image of $(x)$ under the localisation map $A \to A_P$, where $A_P$ is the localisation of $A$ at $P$, generates the whole maximal ideal of $A_P$: $x A_P = P A_P$. The conclusion is that the quotient ring $A/(x)$ is reduced, i.e. it has no non-zero nilpotent elements. Thus the hypothesis is imposed only at the primes minimal over $(x)$, which for a normal Noetherian domain are exactly the height-one primes containing $x$, and it says that $x$ is a uniformiser of each of the corresponding discrete valuation rings.
--
--   This is the standard criterion that a principal hypersurface in a normal Noetherian domain is reduced as soon as it is reduced at the generic points of its components ($R_0$ plus the automatic $S_1$). It is used in the construction of integral models of modular curves, in [`AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal`](thm.html#AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal) and in [`ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH`](thm.html#ModularCurve.XHDRLevel.isReduced_chartAlgFin_quotient_and_chartAlgInf_quotient_span_natCast_gammaH), where $x$ is the residue characteristic and the hypothesis expresses that it is unramified along every component of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ (Ideal.span {x}).minimalPrimes →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) := by sorry
