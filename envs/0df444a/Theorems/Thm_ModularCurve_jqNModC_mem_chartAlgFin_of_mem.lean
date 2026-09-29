-- Prove2me | Theorems.Thm_ModularCurve_jqNModC_mem_chartAlgFin_of_mem
-- name    : ModularCurve.jqNModC_mem_chartAlgFin_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/273ba72a-7455-5d23-af91-e985398823d4
-- title:
--   j(q^N) lies in the j-finite chart algebra
-- statement:
--   Let $L$ be a field of characteristic zero and let $K$ be an intermediate field of the Laurent series field $L((q))$ over $L$. Let $A$ be a commutative domain equipped with an $L$-algebra structure making $L$ its fraction field, and with a compatible algebra structure on $K$ (so $A \to L \to K$ is a tower). Let $j \in K$ be an element whose image in $L((q))$ is $\mathrm{coeffEmb}_L(\mathsf{jq})$, the coefficientwise image along $\mathbb{Q} \to L$ of the rational $q$-expansion $\mathsf{jq} = q^{-1}\cdot(\text{the power series } \mathsf{jNum} \text{ over } \mathbb{Q})$ of the modular invariant, and assume $j \neq 0$. Let $N$ be a nonzero natural number with $N > 1$, and assume that $\mathrm{jqNModC}\, L\, N$, the Laurent series over $L$ obtained from $q^{-1}\cdot \mathsf{jNum}_L$ by the substitution $q \mapsto q^N$ (formally, by `qExpand` on exponents, multiplication of the support degrees by $N$), lies in $K$. Then the corresponding element of $K$ belongs to `chartAlgFin A K j`, that is, it is integral over the $A$-subalgebra $A[j] = \mathrm{Algebra.adjoin}\, A\, \{j\}$ of $K$.
--
--   Classically this is the statement that $j(q^N)$ satisfies the modular equation $\Phi_N(X, j(q)) = 0$, hence is integral over $A[j]$; here it is recorded in the coordinates of the two-chart integral model of a curve, whose finite chart algebra is the integral closure of $A[j]$ in the function field $K$. It feeds the construction of the modular curves of level $N$ and full level within that model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jqNModC_mem_chartAlgFin_of_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.jqNModC_mem_chartAlgFin_of_mem
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (N : ℕ) [NeZero N] (hN : 1 < N) (hK : ModularCurve.jqNModC L N ∈ K) :
    (⟨ModularCurve.jqNModC L N, hK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by sorry
