-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/65e3598f-1a4b-54e9-9f76-b16f89e862e9
-- title:
--   Supersingular fibre points of the two-chart model are maximal
-- statement:
--   Let $q \ge 5$ and $\ell \ge 3$ be primes with $\ell \ne q$, and let $M'$ be a nonzero natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic $0$ containing a primitive $q$-th root of unity $\zeta$ and a primitive $(q\ell)$-th root of unity $\xi$, and assume there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L \subseteq L((\mathsf q))$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of level $\Gamma_H$ over $\mathbb{Q}$, where the level is $(q\ell)^2M'$ and $H = \mathrm{levelH}\,(q\ell)\,M'$ is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$ and algebraically closed residue field, with $q$ in its maximal ideal, $\zeta$ in the image of $A$, and $A$ acting on $K$ compatibly; let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with $q$-expansion the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under the coefficient map $\mathbb{Q} \to L$, and let $\mathfrak X =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout of the two affine charts $\operatorname{Spec}$ of the $A$-algebras of elements of $K$ integral over $A[j]$, respectively over $A[j^{-1}]$. Let $z \in \mathfrak X$ be a point such that the germ at $z$ of the global section coming from $\varpi$ along the structural morphism $\mathfrak X \to \operatorname{Spec} A$ lies in the maximal ideal of the stalk at $z$, and let $y$ be a point of the finite chart $\operatorname{Spec}$ of `chartAlgFin A K j` mapping to $z$. Assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin A K j` to $\Omega$ with kernel exactly the prime $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero point killed by $q$. Then the prime ideal $y$ is maximal in `chartAlgFin A K j`, and the image of $\varpi$ under $A \to$ `chartAlgFin A K j` lies in $y$.
--
--   This identifies the points of the finite chart of the two-chart integral model over $A$ at which the $j$-coordinate is supersingular as closed points of the fibre over the residue characteristic: such a prime is maximal and contains the uniformiser. It is used in the subsequent analysis of the completed stalks of the model at these points, including the computation of the inertial action on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom.lean

import Definitions.Def_ModularCurve_JqCoeff
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

theorem ModularCurve.FullLevel.AuxLevel.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
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
    y.asIdeal.IsMaximal ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by sorry
