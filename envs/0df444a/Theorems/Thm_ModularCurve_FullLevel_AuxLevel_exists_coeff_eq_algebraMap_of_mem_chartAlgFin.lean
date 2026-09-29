-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_coeff_eq_algebraMap_of_mem_chartAlgFin
-- name    : ModularCurve.FullLevel.AuxLevel.exists_coeff_eq_algebraMap_of_mem_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/8f58a00a-413a-5f04-b581-959a6685fb27
-- title:
--   Integrality of q-expansion coefficients on the finite chart
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \ge 3$, $\ell \neq q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L(\!(X)\!)$ (Laurent series over $L$) equal to [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the $q$-expansion function field `xHFunctionField` of level $(q\ell)^2 M'$ and group `levelH (q*ℓ) M'`, that is: $K$ is generated over $L$ by the coefficientwise images in $L(\!(X)\!)$ of the elements of the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}(\!(X)\!)$ attached to $\Gamma_H((q\ell)^2M')$, where $H$ is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation ring, an $A$-algebra structure on $L$ making $L$ the fraction field of $A$, with $q$ in the maximal ideal of $A$ and $\zeta$ in the image of $A \to L$, and let $K$ be an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be nonzero and have Laurent series equal to the image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= X^{-1} \cdot \sum_n a_n X^n$, the rational $q$-expansion of the modular $j$-invariant. Then for every $x$ in the subalgebra `chartAlgFin A K j` of elements of $K$ integral over $A[j] =$ `Algebra.adjoin A {j}`, and every $n \in \mathbb{Z}$, the $n$-th Laurent coefficient of $x$ lies in the image of $A \to L$.
--
--   This is the $q$-expansion principle at the cusp $\infty$ for the chart of the two-chart integral model on which $j$ is finite: integrality over $A[j]$ forces all $q$-expansion coefficients to be integral. It feeds the description of the local behaviour of the auxiliary-level two-chart integral model, being used in [`ModularCurve.FullLevel.AuxLevel.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_of_linearPart_riders_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_of_linearPart_riders_twoChartIntegralModel); the proof rests on the existence of the Gauss valuation subring of $K$ supplied by [`ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC`](thm.html#ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_coeff_eq_algebraMap_of_mem_chartAlgFin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_coeff_eq_algebraMap_of_mem_chartAlgFin
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
 :
    ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (n : ℤ), ∃ m : A, ((x : ↥K) : LaurentSeries L).coeff n = algebraMap A L m := by sorry
