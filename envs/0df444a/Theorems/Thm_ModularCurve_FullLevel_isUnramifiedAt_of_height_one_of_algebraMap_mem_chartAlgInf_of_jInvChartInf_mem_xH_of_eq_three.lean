-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
-- name    : ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/0064e267-82b9-5525-b649-72725462ed64
-- title:
--   Unramifiedness at vertical height-one primes over cusps, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, and let $\zeta \in L$ be a primitive $q$-th root of unity; it is assumed that there is a ring homomorphism $L \to \mathbb{C}$ carrying $\zeta$ to $\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L \subseteq L((t))$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_H(q^2M')$, where $H \le (\mathbb{Z}/q^2M')^\times$ is the kernel of reduction to $(\mathbb{Z}/q)^\times$ (that field being generated over $\mathbb{Q}$ by quotients of integral $q$-expansions of modular forms of equal weight for that group). Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, and with uniformiser $\varpi$ generating the maximal ideal; $K$ is an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$, nonzero, whose Laurent series is the coefficientwise image of the $q$-expansion $q^{-1}(1+\cdots)$ of the modular $j$-function. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ in $L((t))$ after mapping coefficients to $L$. Write $A_\infty(K)$ for the subalgebra of elements of $K$ integral over $A[j^{-1}]$, and let $X_\infty = \operatorname{Spec} A_\infty(K)$; the two-chart integral model of $(A,K,j)$ is the pushout of the two maps from the middle chart to the spectra of the charts for $j$ and $j^{-1}$. Let $z$ be a point of that model at which the germ of the image of $\varpi$ under the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk, and let $y \in X_\infty$ be a point with maximal prime ideal $\mathfrak p_y$ mapping to $z$ under the canonical morphism $X_\infty \to$ (model). Assume $y$ is a cusp of the $j^{-1}$-chart, in the sense that $j^{-1} \in \mathfrak p_y$, and that every element of $A_\infty(K)$ whose image in $K$ is a nonunit of $W_0$ lies in $\mathfrak p_y$. Let $K_0 \le K$ be the analogous intermediate field for $\Gamma_0(M')$, with $A$-algebra structure as above, and let $j_0 \in K_0$ be nonzero with the same Laurent expansion; let $\iota : A_\infty(K_0) \to A_\infty(K)$ be a ring homomorphism compatible with the inclusion $K_0 \hookrightarrow K$ on underlying elements. Then, for the algebra structure on $A_\infty(K)$ given by $\iota$, every prime ideal $\mathfrak Q$ of $A_\infty(K)$ with $\mathfrak Q \subseteq \mathfrak p_y$, of height $1$, and containing the image of $\varpi$, satisfies $\mathbf{Algebra.IsUnramifiedAt}$ for $A_\infty(K_0) \to A_\infty(K)$ at $\mathfrak Q$.
--
--   This is the cusp case, on the $j^{-1}$-chart (the pole chart) of the two-chart integral model, of the statement that the covering of the level-$M'$ floor by the level-$\Gamma_H(q^2M')$ curve is unramified at the vertical height-one primes below a special cusp point, in the residue characteristic $q = 3$; for $q = 3$ the relevant covering of the $\infty$-branch is degenerate, so the assertion holds with the level structure contributing nothing. It feeds the regularity analysis of the special fibre of the pole chart at such points, [`ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three`](thm.html#ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three.lean

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

theorem ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
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
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) 𝔔 := by sorry
