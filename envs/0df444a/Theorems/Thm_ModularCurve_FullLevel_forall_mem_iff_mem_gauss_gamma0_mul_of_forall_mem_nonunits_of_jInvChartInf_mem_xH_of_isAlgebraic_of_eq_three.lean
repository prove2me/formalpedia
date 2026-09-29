-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three
-- name    : ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/d88146cc-d11d-5e29-a5ab-b0d6e4d6c463
-- title:
--   Cusp of the ∞-branch lies over the X₀(qM') Gauss ring, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$, a natural number $M' \neq 0$ with $q \nmid M'$, and a field $L$ of characteristic zero, algebraic over $\mathbb{Q}$, carrying a primitive $q$-th root of unity $\zeta$ and admitting a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $X_H$ function field of level $q^2M'$ for $H$ the kernel of $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, $\zeta$ in the image of $A$, uniformiser $\varpi$, and with an $A$-algebra structure on $K$ compatible with $A \to L \to K$; let $j \in K$ be nonzero with underlying Laurent series the coefficientwise image of the $q$-expansion $j_q$. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are $x, y \in A[[T]]$ with $y$ nonzero modulo the maximal ideal of $A$ and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$. Let $z$ be a point of the two-chart integral model $\mathfrak{X} =$ `TwoChartIntegralModel A K j` at which the germ of the global section of $\mathfrak{X}$ coming from $\varpi$ via the structure morphism to $\mathrm{Spec}\,A$ lies in the maximal ideal of the stalk, and let $y$ be a point of $\mathrm{Spec}$ of the subalgebra `chartAlgInf A K j` of elements of $K$ integral over $A[j^{-1}]$, mapping to $z$ under `ιInf`, with maximal prime ideal $\mathfrak{p}_y$, such that $j^{-1} \in \mathfrak{p}_y$ and such that every element of `chartAlgInf A K j` which is a non-unit of $W_0$ lies in $\mathfrak{p}_y$. Let $K_0 \subseteq K_0' \subseteq K$ be the intermediate fields obtained by adjoining to $L$ the coefficientwise images of the $q$-expansion function fields of $\Gamma_0(M')$ and $\Gamma_0(qM')$, with valuation subrings $O_0 \subseteq K_0$ and $O_0' \subseteq K_0'$ described by the same power-series condition as $W_0$. Then for every valuation subring $B$ of $K$ such that an element of $K_0$ maps into $B$ exactly when it lies in $O_0$, and such that every element of `chartAlgInf A K j` whose image in $K$ is a non-unit of $B$ lies in $\mathfrak{p}_y$, an element of $K_0'$ maps into $B$ exactly when it lies in $O_0'$.
--
--   This is the cusp-side (pole-chart) case, for $q = 3$, of the statement that a vertical valuation of $K$ centred at a cusp on the $\infty$-branch of the integral model and lying over the Gauss ring of the $\Gamma_0(M')$-level field already lies over the Gauss ring of the $\Gamma_0(qM')$-level field; it is the companion of the corresponding result for $q \geq 5$. It feeds the unramifiedness statement [`ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three`](thm.html#ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three) in the analysis of the special fibre of the modular curve of level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three.lean

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

theorem ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three
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
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)

    (hcusp : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j ∈ y.asIdeal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

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
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ B.nonunits → b ∈ y.asIdeal) →
        ∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀' := by sorry
