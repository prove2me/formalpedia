-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/0648deb3-533e-55f7-ab77-37dbae864ab7
-- title:
--   Two special-fibre components through a supersingular point
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'\neq 0$ be a natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta\in L$ be a primitive $q$-th root of unity and $\xi\in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L(\!(T)\!)$ generated over $L$ by the coefficientwise image of the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2M'$ with subgroup [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\zeta$ in the image of $A$, acting on $K$ compatibly, and let $\varpi$ generate the maximal ideal of $A$. Let $j\in K$ be nonzero with underlying Laurent series the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function. Write $C=$ `chartAlgFin A K j`, the subalgebra of elements of $K$ integral over $A[j]$, and let $X$ be the two-chart integral model, the pushout of the two maps from the middle chart to $\operatorname{Spec}$ of the $j$-finite and $j^{-1}$-finite chart algebras. Let $z$ be a point of $X$ such that the image $\varpi_z$ of $\varpi$ in the stalk $\mathcal{O}_{X,z}$, obtained along the structure morphism $X\to\operatorname{Spec}A$ and the germ map, lies in the maximal ideal of that stalk, and let $y\in\operatorname{Spec}C$ map to $z$ under the chart inclusion. Assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi\colon C\to\Omega$ with kernel exactly the prime of $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $\jmath\in\Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\jmath$ has no nonzero point killed by $q$. Then there exist two distinct prime ideals $G\neq G'$ of $C$, both containing the image of $\varpi$, both contained in the prime of $y$ and both different from it.
--
--   In geometric terms: at least two irreducible components of the special fibre $\operatorname{Spec}(C/\varpi C)$ of the two-chart integral model pass through each supersingular point, the phenomenon identified for Igusa-type models of modular curves with full level structure at $q$ by Igusa and by Katz–Mazur. It feeds the analysis of the local ring at such a point, being used to show that the relevant quotient of the stalk at $z$ is a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel
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
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    ∃ G G' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      G.IsPrime ∧ G'.IsPrime ∧ G ≠ G' ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ G ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ G' ∧
      G ≤ y.asIdeal ∧ G' ≤ y.asIdeal ∧ G ≠ y.asIdeal ∧ G' ≠ y.asIdeal := by sorry
