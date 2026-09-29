-- Prove2me | Theorems.Thm_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
-- name    : ModularCurve.coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/7270a72f-c6f8-5944-9385-906910605830
-- title:
--   Integral j-chart ring lies in valuation subrings containing A[j]
-- statement:
--   Let $L$ be a field of characteristic zero, let $K$ be an intermediate field of the extension $L \subseteq L((q))$ of $L$ by the field of formal Laurent series over $L$, and let $A$ be a discrete valuation domain equipped with an $A$-algebra structure on $L$ making $L$ the fraction field of $A$, together with an $A$-algebra structure on $K$ compatible with that of $L$ via the scalar tower $A \to L \to K$. Fix $j \in K$, assumed nonzero (as a `Fact` instance), and a valuation subring $W_0$ of $K$. Assume that $W_0$ contains the image of $A$ under the structure map $A \to K$, and that for every polynomial $P \in A[X]$ whose reduction modulo the maximal ideal of $A$ (the image of $P$ under the residue map of the local ring $A$) is nonzero, the value $P(j)$ lies in $W_0$. The conclusion is that every element of the $A$-subalgebra `chartAlgFin A K j` of $K$ — by definition the set of elements of $K$ integral over the $A$-subalgebra $A[j] =$ `Algebra.adjoin A {j}`, that is, the integral closure of $A[j]$ in $K$ — lies in $W_0$.
--
--   This is the containment of the finite ($j$-integral) chart ring of the two-chart integral model in a prescribed valuation subring of $K$: the integral closure of $A[j]$ in $K$ sits inside any valuation subring that contains the constants $A$ and the values at $j$ of the polynomials over $A$ with nonzero reduction. It is used, with $W_0$ a Gauss valuation subring of a field of $q$-expansions, as the hypothesis 'the chart ring lies in the Gauss ring' in the results on the special-fibre sheet of the integral model of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hAW₀ : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hjW₀ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j P ∈ W₀) :
    ∀ s : ↥(chartAlgFin A (↥K) j), (s : ↥K) ∈ W₀ := by sorry
