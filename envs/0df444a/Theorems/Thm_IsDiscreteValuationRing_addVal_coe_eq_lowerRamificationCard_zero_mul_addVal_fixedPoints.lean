-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
-- name    : IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/170b7bbc-1aa2-58b9-baff-3c38818ed372
-- title:
--   Valuation on a DVR restricted to its fixed subring
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $H$ be a finite group acting on $R$ by ring automorphisms, the action being faithful. Assume that the subring $R^H$ of $H$-fixed points, `FixedPoints.subring R H`, is itself a discrete valuation ring, that the maximal ideal of $R$ lies over the maximal ideal of $R^H$, and that the residue field extension $R^H/\mathfrak m_{R^H} \to R/\mathfrak m_R$ is separable. Write $\mathrm{addVal}$ for the normalised additive valuation of a discrete valuation ring, with values in $\mathbb N\cup\{\infty\}$. Then for every $z \in R^H$, the valuation of the image of $z$ in $R$ satisfies
--   $$\mathrm{addVal}_R(z) = \big(\#\,H_0\big)\cdot \mathrm{addVal}_{R^H}(z),$$
--   the product being taken in $\mathbb N\cup\{\infty\}$, where $\#\,H_0$ is [`IsLocalRing.lowerRamificationCard R H 0`](def/Mathlib_RingTheory_Valuation_UpperRamificationGroup.html#L13), namely the cardinality of the zeroth lower ramification group of the action, defined as the inertia subgroup of $H$ attached to the ideal $\mathfrak m_R$, i.e. the subgroup of those $\sigma \in H$ that stabilise $\mathfrak m_R$ and act trivially on $R/\mathfrak m_R$.
--
--   This is the classical identity $v_R|_{R^H} = e\, v_{R^H}$ together with the identification of the ramification index $e$ with the order of the inertia group, in the setting of a finite group acting on a discrete valuation ring with separable residue extension; in the Galois case $R=\mathcal O_L$, $H=\mathrm{Gal}(L/K)$ it is the statement $v_L|_K = e_{L/K} v_K$ with $e_{L/K} = \#\mathrm{Gal}(L/K)_0$. It supplies the normalisation of valuations used in the lemmas on lower and upper ramification groups that approximate elements of $\mathfrak m_R^n$ by sums of Galois translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] [FaithfulSMul H R]
    [IsDiscreteValuationRing (FixedPoints.subring R H)]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R H))]
    [Algebra.IsSeparable
      (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (z : FixedPoints.subring R H) :
    IsDiscreteValuationRing.addVal R (z : R) =
      (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
        IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z := by sorry
