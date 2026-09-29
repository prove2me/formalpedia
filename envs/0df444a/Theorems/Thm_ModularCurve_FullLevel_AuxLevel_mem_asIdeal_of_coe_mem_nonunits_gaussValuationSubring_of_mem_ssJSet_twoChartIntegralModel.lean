-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/e3ef2b81-a399-5f65-bdb0-fd7d2c2d6562
-- title:
--   Gauss-nonunits of the finite chart lie in supersingular primes
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \neq q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_H$ at level $(q\ell)^2 M'$, where $H =$ [`ModularCurve.FullLevel.levelH (q*ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A \to L$, with $A$ acting on $K$ compatibly through $L$; let $\varpi \in A$ generate the maximal ideal. Let $j \in K$ be nonzero with Laurent expansion the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function. Write $C =$ [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) for the subalgebra of elements of $K$ integral over $A[j]$, and let $X$ be the two-chart integral model, the pushout of $\operatorname{Spec}$ of the mid chart over $\operatorname{Spec} C$ and $\operatorname{Spec}$ of the integral closure of $A[j^{-1}]$. Let $z$ be a point of $X$ such that the germ at $z$ of the global section of $X$ obtained from $\varpi$ along the structure morphism $X \to \operatorname{Spec} A$ lies in the maximal ideal of the stalk at $z$, and let $y$ be a point of $\operatorname{Spec} C$ mapping to $z$ under the canonical morphism. Assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero affine point killed by $q$. Finally let $W_0$ be a valuation subring of $K$ characterised by: $f \in W_0$ if and only if there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$ after applying $A \to L$ coefficientwise. Then every $h \in C$ whose image in $K$ is a nonunit of $W_0$ lies in the prime ideal of $y$.
--
--   This is the local statement that the maximal ideal of the Gauss valuation ring $W_0$ of $A$ in $K$ meets the finite chart algebra inside the prime attached to a supersingular point of the special fibre, in the style of the theory of supersingular points on integral models of modular curves. It is used in the proof of [`ModularCurve.FullLevel.AuxLevel.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel), which produces two distinct primes of the chart algebra above supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel.lean

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

theorem ModularCurve.FullLevel.AuxLevel.mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel
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
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hh : ((h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits) :
    h ∈ y.asIdeal := by sorry
