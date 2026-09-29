-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_two
-- name    : ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/8ba0e059-17fe-5cae-8ad4-3b2c2428e450
-- title:
--   Descent of the Gauss valuation to Γ₀(qM') at ordinary points, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ for which there is a ring embedding $\iota:L\to\mathbb{C}$ with $\iota(\zeta)=\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $q^2M'$ for the subgroup $H=\ker\bigl((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\bigr)$, i.e. the field generated over $L$ by the coefficientwise image of that field of $q$-expansions. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $L$; let $\varpi$ generate the maximal ideal of $A$, and let $j\in K$ be nonzero with underlying Laurent series the coefficient embedding of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the $j$-invariant. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f\cdot y = x$ in $\mathrm{LaurentSeries}\,L$. On the two-chart integral model $\mathfrak X=$ [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) $A$ $K$ $j$ (the pushout of the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$), let $z$ be a point at which the germ of the global section coming from $\varpi$ lies in the maximal ideal of the stalk, and let $y$ be a point of $\mathrm{Spec}$ of the finite chart algebra `chartAlgFin` mapping to $z$, with $y$ given by a maximal ideal. Let $\Omega$ be an algebraically closed field of characteristic $q$ and $\varphi:$ `chartAlgFin` $\to\Omega$ a ring homomorphism with kernel the ideal of $y$, such that $\varphi(j)$ does not lie in [`ModularCurve.ssJSet`](def/ModularCurve_SupersingularModuli.html#L7) $q$ $\Omega$, that is, some elliptic curve over $\Omega$ with that $j$-invariant has a nonzero point killed by $q$. Assume further that every element of `chartAlgFin` whose image in $K$ is a nonunit of $W_0$ lies in the ideal of $y$. Let $K_0$ and $K_0'$ be the `laurentBaseChange` to $L$ of the $q$-expansion function fields `qExpFunctionFieldC` of $\Gamma_0(M')$ and of $\Gamma_0(qM')$, with $K_0\le K_0'\le K$, and let $O_0\subseteq K_0$, $O_0'\subseteq K_0'$ be the valuation subrings described by the same power-series condition as $W_0$. Then, for the algebra structures on $K$ over $K_0$ and $K_0'$ given by the inclusions, every valuation subring $B$ of $K$ such that $B\cap K_0=O_0$ (an element of $K_0$ lies in $B$ exactly when it lies in $O_0$) and such that every element of `chartAlgFin` whose image in $K$ is a nonunit of $B$ lies in the ideal of $y$ satisfies $B\cap K_0'=O_0'$: an element of $K_0'$ lies in $B$ exactly when it lies in $O_0'$.
--
--   This is the $q=2$ instance of the statement that, at a closed point of the special fibre of the two-chart integral model lying on the $W_0$-branch and with ordinary $j$-invariant, any valuation ring of the level-$q^2M'$ field restricting to the Gauss valuation of the $\Gamma_0(M')$-floor and centred at that point already restricts to the Gauss valuation of the $\Gamma_0(qM')$-floor. It feeds the unramifiedness statement [`ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_two`](thm.html#ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_two) in the analysis of the Igusa tower over $\Gamma_0(qM')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_two.lean

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

theorem ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_two
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
    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀ : K₀ ≤ K₀') (hle' : K₀' ≤ K)
    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (O₀' : ValuationSubring ↥K₀')
    (hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion (hle₀.trans hle')).toRingHom.toAlgebra
    letI : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
    ∀ (B : ValuationSubring ↥K),
      (∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀) →
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ B.nonunits → b ∈ y.asIdeal) →
        ∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀' := by sorry
