-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three
-- name    : ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/7d73b77f-66ce-517c-a236-fa53f17e5e22
-- title:
--   Ordinary branches lie over the Γ₀(qM') Gauss ring, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a nonzero natural number $M'$ with $q \nmid M'$; let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ for which there is a ring homomorphism $L \to \mathbb{C}$ sending $\zeta$ to $\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $\mathbb{Q}$-field of $q$-expansion ratios of integral modular forms for $\Gamma_H(q^2M')$, where $H =$ [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly with $L$, and let $\varpi$ generate its maximal ideal. Let $j \in K$ be nonzero with Laurent expansion the image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$. On the two-chart integral model $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout of the two charts $\operatorname{Spec}$ of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$) let $z$ be a point at which the image $\varpi_z$ of $\varpi$ under $\Gamma(\operatorname{Spec} A) \to \Gamma(\mathfrak{X}) \to \mathcal{O}_{\mathfrak{X},z}$ lies in the maximal ideal, and let $y$ be a point of the finite chart $\operatorname{Spec}(\mathrm{chartAlgFin}\,A\,K\,j)$ with maximal prime $\mathfrak{p}_y$ mapping to $z$. Assume there is a ring homomorphism $\varphi$ from the finite chart algebra to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $\mathfrak{p}_y$ such that $\varphi(j) \notin$ [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, some elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has a nonzero point killed by $q$; and assume every element of the finite chart algebra that is a nonunit of $W_0$ lies in $\mathfrak{p}_y$. Let $K_0 \subseteq K_0' \subseteq K$ be the base changes to $L$ of the $q$-expansion fields of $\Gamma_0(M')$ and of $\Gamma_0(qM')$, with $O_0 \subseteq K_0$ and $O_0' \subseteq K_0'$ the valuation subrings described by the same power-series condition as $W_0$. Then, with $K$ viewed as an algebra over $K_0$ and over $K_0'$ via these inclusions, for every valuation subring $B$ of $K$ such that an element of $K_0$ lies in $B$ exactly when it lies in $O_0$, and such that every element of the finite chart algebra which is a nonunit of $B$ lies in $\mathfrak{p}_y$, an element of $K_0'$ lies in $B$ exactly when it lies in $O_0'$.
--
--   This is the step, in the analysis of the Igusa-type integral model of the modular curve of level $q^2M'$, that propagates the Gauss valuation from the $\Gamma_0(M')$ floor to the $\Gamma_0(qM')$ floor along any branch of the special fibre through an ordinary closed point of the chosen branch; it is the case $q = 3$ of the statement, the case $q \ge 5$ being treated separately. It is used in the proof of [`ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_three`](thm.html#ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_xH_of_isAlgebraic_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three.lean

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

theorem ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
