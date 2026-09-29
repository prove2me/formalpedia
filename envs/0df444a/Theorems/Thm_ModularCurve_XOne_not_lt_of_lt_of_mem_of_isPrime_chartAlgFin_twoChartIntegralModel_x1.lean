-- Prove2me | Theorems.Thm_ModularCurve_XOne_not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
-- name    : ModularCurve.XOne.not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/42366fa8-6a86-5b02-a56f-245748ecd6b6
-- title:
--   No three-step prime chain above varpi in the finite chart
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$; let $L$ be a field of characteristic $0$, and let $A$ be a discrete valuation domain with $L$ as its fraction field, $\varpi \in A$ irreducible. Let $K_M$ be the intermediate field of $L((q)) =$ `LaurentSeries L` over $L$ obtained as [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the image, under the coefficientwise map $\mathbb{Q}((q)) \to L((q))$, of the $q$-expansion function field `x1FunctionFieldC ℚ (Gamma1 M)`; $K_M$ is an $A$-algebra compatibly with $A \to L \to K_M$. Let $j_M \in K_M$ be nonzero with $q$-expansion the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under that coefficient map. Consider the ring `chartAlgFin A K_M j_M`, the $A$-subalgebra of $K_M$ consisting of the elements integral over $A[j_M] =$ `Algebra.adjoin A {j_M}`. The assertion is that for all prime ideals $\mathfrak{q}, \mathfrak{p}', \mathfrak{m}$ of this ring, if the image of $\varpi$ lies in $\mathfrak{q}$ and $\mathfrak{q} \subsetneq \mathfrak{p}'$, then $\mathfrak{p}' \subsetneq \mathfrak{m}$ fails.
--
--   This is the Krull-dimension bookkeeping for the affine $j$-finite chart of the integral model of $X_1(M)$ over a discrete valuation ring: no prime containing the uniformiser can be the bottom of a chain of three strict inclusions, so the fibre over $\varpi$ has dimension one. It is used in the construction and analysis of that chart, in particular for the finiteness and flatness statement, for the identification of the local rings at height-one primes as discrete valuation rings, and for a membership criterion in terms of the Gauss valuation subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOne_not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XOne.not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (ϖ : A) (hϖ : Irreducible ϖ)
    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)] :
    ∀ 𝔮 𝔭' m : Ideal ↥(chartAlgFin A (↥K_M) j_M), 𝔮.IsPrime → 𝔭'.IsPrime → m.IsPrime →
      algebraMap A _ ϖ ∈ 𝔮 → 𝔮 < 𝔭' → ¬ 𝔭' < m := by sorry
