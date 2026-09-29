-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet
-- name    : ModularCurve.FullLevel.AuxLevel.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/d597c868-4337-5b8a-8618-d33fe6213535
-- title:
--   Supersingular chart points are closed and carry the uniformiser
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero which is a $\{q\ell\}$-cyclotomic extension of $\mathbb{Q}$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image under `coeffEmb L` of the $q$-expansion function field `xHFunctionField ((q*ℓ)^2 * M') (levelH (q*ℓ) M')`, the level subgroup being the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$, that is the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and with $\zeta$ in the image of $A \to L$, and let $K$ be an $A$-algebra compatibly with the tower $A \to L \to K$. Let $j \in K$ be nonzero with image in $\mathrm{LaurentSeries}\,L$ the $q$-expansion `coeffEmb L jq` of the modular $j$-function, and let $\varpi$ generate the maximal ideal of $A$. Write $X =$ `TwoChartIntegralModel A K j`, the pushout gluing $\operatorname{Spec}$ of the integral closure $C$ of $A[j]$ in $K$ to $\operatorname{Spec}$ of the integral closure of $A[j^{-1}]$ in $K$. Let $z$ be a point of $X$ such that the germ at $z$ of the global section of $X$ obtained from $\varpi$ along the structure morphism $X \to \operatorname{Spec} A$ lies in the maximal ideal of the local ring of $X$ at $z$, and let $y$ be a point of $\operatorname{Spec} C$ with $\iota_{\mathrm{Fin}}(y) = z$. Assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel exactly the prime $y$, the value $\varphi(j)$ lies in `ssJSet q Ω`, the set of $j$-invariants such that every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $q$-torsion point. Then the prime $y$ is a maximal ideal of $C$ and the image of $\varpi$ under $A \to C$ lies in $y$.
--
--   This says that a point of the $j$-finite chart of the two-chart integral model at which $j$ specialises to a supersingular value is a closed point lying in the special fibre over the residue characteristic $q$. It is the input for the local analysis at supersingular points, where the stalk of the model is identified with a localisation of $C$ and then with an adic completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet.lean

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

theorem ModularCurve.FullLevel.AuxLevel.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet
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
    y.asIdeal.IsMaximal ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by sorry
