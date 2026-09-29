-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isDiscreteValuationRing_stalk_quotient_of_mem_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.isDiscreteValuationRing_stalk_quotient_of_mem_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/81f37e7e-3267-5980-a6ac-29dfd91abb16
-- title:
--   Special-fibre components are discrete valuation rings at supersingular points
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'$ be a nonzero natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with $\zeta\in L$ a primitive $q$-th root of unity and $\xi\in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}(L)$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of level $(q\ell)^2M'$ attached to the subgroup of $(\mathbb{Z}/(q\ell)^2M')^\times$ of units congruent to $1$ modulo $q\ell$ (the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$). Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A\to L$, with $A$ acting on $K$ compatibly, and let $\varpi$ generate the maximal ideal of $A$. Let $j\in K$ be nonzero with Laurent expansion the coefficientwise image of the $j$-series $q^{-1}+\cdots$. Consider the two-chart integral model $\mathfrak X$ over $A$: the pushout of the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$ along the middle chart. Let $z\in\mathfrak X$, let $\varpi_z$ be the germ at $z$ of the global function coming from $\varpi$ under the structure morphism to $\operatorname{Spec} A$, and assume $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal O_{\mathfrak X,z}$. Assume $z$ is the image of a point $y$ of $\operatorname{Spec}$ of the finite chart algebra, and that $y$ is supersingular in the following sense: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the finite chart algebra to $\Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in $\mathrm{ssJSet}\,q\,\Omega$, that is, every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. Then for every prime ideal $Q$ of $\mathcal O_{\mathfrak X,z}$ containing $\varpi_z$ and not maximal, the quotient $\mathcal O_{\mathfrak X,z}/Q$ is a discrete valuation ring.
--
--   The primes $Q$ in question are the generic points of the irreducible components of the special fibre $\mathfrak X\otimes_A A/\varpi$ passing through the supersingular point $z$, so the statement asserts that each such component is regular at $z$ — the Igusa-component picture of the special fibre of a full-level modular curve over a ramified base at a supersingular point. It feeds the proof that two distinct branch primes of the completed stalk cannot contract to the same prime of the stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_isDiscreteValuationRing_stalk_quotient_of_mem_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel.lean

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

theorem ModularCurve.FullLevel.AuxLevel.isDiscreteValuationRing_stalk_quotient_of_mem_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel
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

    ∀ (Q : Ideal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) [Q.IsPrime],
      ϖz ∈ Q → ¬ Q.IsMaximal →
        IsDiscreteValuationRing (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Q) := by sorry
