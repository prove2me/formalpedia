-- Prove2me | Theorems.Thm_IsCyclotomicExtension_Rat_isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing
-- name    : IsCyclotomicExtension.Rat.isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/6e668849-1859-577e-be05-820d15f0cee0
-- title:
--   DVRs of ℚ(ζₚ) containing p in the maximal ideal
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, so that $L$ is generated over $\mathbb{Q}$ by a primitive $p$-th root of unity. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an $A$-algebra structure on $L$ making $L$ a fraction field of $A$, and assume that the image of $p$ in $A$ lies in the maximal ideal of the local ring $A$. Then for every $y \in L$ the following two conditions are equivalent: $y$ is integral over the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$, whose elements are the rational numbers whose denominator is coprime to $p$ (that is, the localisation $\mathbb{Z}_{(p)}$ of $\mathbb{Z}$ away from $p$, realised inside $\mathbb{Q}$); and $y$ lies in the image of the structure map $A \to L$, i.e. there exists $a \in A$ with $\mathrm{algebraMap}\,a = y$. Equivalently, such an $A$ is exactly the integral closure of $\mathbb{Z}_{(p)}$ in $L$.
--
--   This identifies any discrete valuation ring with fraction field $\mathbb{Q}(\zeta_p)$ in which $p$ is not a unit with the localisation at $p$ of the ring of integers, $\mathbb{Z}_{(p)}[\zeta_p]$, using that $p$ is totally ramified in $\mathbb{Q}(\zeta_p)$. It is used to recognise the base rings occurring in the integral models of the modular curve of level $p$, in [`ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension`](thm.html#ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension), [`ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_conorm_laurentPlaceReduction_of_points_of_gaussReading_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.addEquiv_proj_fst_eq_pic0Mk_conorm_laurentPlaceReduction_of_points_of_gaussReading_twoChartModel_x1_mul) and [`ModularCurve.XOne.smooth_toBase_and_isIntegral_pullback_twoChartIntegralModel_x1`](thm.html#ModularCurve.XOne.smooth_toBase_and_isIntegral_pullback_twoChartIntegralModel_x1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_Rat_isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.Rat.isIntegral_ratLocalizedAt_iff_exists_algebraMap_eq_of_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (y : L) :
    IsIntegral ↥(GaloisRep.ratLocalizedAt p) y ↔ ∃ a : A, algebraMap A L a = y := by sorry
