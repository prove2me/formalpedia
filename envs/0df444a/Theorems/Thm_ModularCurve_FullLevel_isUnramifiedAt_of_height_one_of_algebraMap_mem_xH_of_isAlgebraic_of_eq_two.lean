-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_two
-- name    : ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/354bcb51-d448-5215-9ded-6d13fd0118ca
-- title:
--   Unramified over X₀(M') at ordinary Igusa-branch height-one primes, q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a non-zero $M'$ with $q\nmid M'$, and a field $L$ of characteristic zero, algebraic over $\mathbb Q$, containing a primitive $q$-th root of unity $\zeta$ and admitting a ring embedding into $\mathbb C$ carrying $\zeta$ to $e^{2\pi i/q}$. Let $K$ be the intermediate field of $L\subseteq$ `LaurentSeries L` obtained by adjoining to $L$ the coefficientwise image of the $\mathbb Q$-rational $q$-expansion function field of level $q^2M'$ and group $H=\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\big)$, and let $A$ be a discrete valuation ring with fraction field $L$, with $q\in\mathfrak m_A=(\varpi)$ and $\zeta$ in the image of $A$, the $A$-algebra structure on $K$ being compatible with $L$. Let $j\in K$ be non-zero with Laurent expansion the coefficientwise image of the $q$-expansion of the modular invariant, and let $W_0$ be the valuation subring of $K$ consisting of those $f$ with $f\cdot y=x$ for power series $x,y$ over $A$ with $y\not\equiv0$ modulo $\mathfrak m_A$. Write $\mathfrak X$ for the two-chart integral model over $A$ attached to $(K,j)$, the pushout of the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$. Let $z\in\mathfrak X$ be a point at which the germ of the global section obtained from $\varpi$ along $\mathfrak X\to\operatorname{Spec}A$ lies in the maximal ideal of the stalk, let $y$ be a point of the spectrum of the $j$-finite chart algebra $C=$ integral closure of $A[j]$ in $K$ mapping to $z$, with $y$ maximal, and assume: there is a ring homomorphism $\varphi$ from $C$ to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $y$ such that $\varphi(j)$ is not in `ssJSet q Ω`, i.e. some elliptic curve over $\Omega$ with that $j$-invariant has a non-trivial point killed by $q$; and every element of $C$ whose image in $K$ is a non-unit of $W_0$ lies in $y$. Let $K_0\le K$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_0(M')$ over $\mathbb Q$, with $j_0\in K_0$ non-zero having the same Laurent expansion as $j$, let $C_0$ be the integral closure of $A[j_0]$ in $K_0$, and let $\iota:C_0\to C$ be a ring homomorphism inducing on elements the inclusion $K_0\subseteq K$. Then, with $C$ a $C_0$-algebra via $\iota$, for every prime ideal $\mathfrak Q$ of $C$ with $\mathfrak Q\subseteq y$, $\operatorname{height}\mathfrak Q=1$ and $\varpi\in\mathfrak Q$, the algebra $C$ is unramified over $C_0$ at $\mathfrak Q$.
--
--   This is the vertical unramifiedness statement on the branch of the special fibre cut out by the Gauss valuation ring $W_0$: at a closed point of the special fibre with ordinary $j$-invariant lying on that branch, the $j$-finite chart of the integral model of the level-$q^2M'$ curve is unramified over the corresponding chart of the level-$M'$ floor at every height-one prime containing the uniformiser of $A$. It is the $q=2$ case, proved without any rigidity guard, and it feeds the verification that the local rings of the special fibre at such points are regular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_two.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔 := by sorry
