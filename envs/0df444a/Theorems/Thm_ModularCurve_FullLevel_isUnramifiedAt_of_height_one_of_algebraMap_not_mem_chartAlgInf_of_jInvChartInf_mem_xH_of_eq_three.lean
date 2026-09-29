-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
-- name    : ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/e13dfcfc-931c-5acd-b245-7051a6f58707
-- title:
--   Horizontal unramifiedness over the X₀(M') floor at ∞-branch cusps, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$ and a nonzero natural number $M'$ with $q \nmid M'$. Let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing an element $\zeta$ that is a primitive $q$-th root of unity, and assume there is a ring homomorphism $L \to \mathbb{C}$ carrying $\zeta$ to $\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L \subseteq L((T))$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), that is the field generated over $L$ by the coefficientwise image of the function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $q^2M'$ for the subgroup $H = \ker\big((\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times\big)$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, acting on $K$ compatibly; let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with Laurent expansion the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. Let $W_0$ be a valuation subring of $K$ characterised by: $f \in W_0$ exactly when there are power series $x, y$ over $A$ with $y$ nonzero modulo the maximal ideal of $A$ and $f \cdot y = x$ after mapping coefficients to $L$. Write $B =$ `chartAlgInf` $A$ $K$ $j$, the integral closure of $A[j^{-1}]$ in $K$, and `XInf` $=\operatorname{Spec} B$; let $z$ be a point of the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) $A$ $K$ $j$ (the pushout gluing the $j$- and $j^{-1}$-charts) at which the germ $\varpi_z$ of the image of $\varpi$ under the structure map to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk, and let $y \in$ `XInf` be a point with maximal prime $y$, mapping to $z$, such that $j^{-1}$ (as the element `jInvChartInf` of $B$) lies in $y$ and such that every $b \in B$ whose image in $K$ is a nonunit of $W_0$ lies in $y$. Let $K_0$ be the base change to $L$ of the $q$-expansion function field of $\Gamma_0(M')$ over $\mathbb{Q}$, with $K_0 \le K$ and compatible $A$-algebra structures, let $j_0 \in K_0$ be nonzero with the same Laurent expansion as $j$, and let $\iota$ be a ring homomorphism from `chartAlgInf` $A$ $K_0$ $j_0$ to $B$ inducing the inclusion $K_0 \hookrightarrow K$ on underlying elements, used as the algebra structure. Then for every prime ideal $\mathfrak{Q}$ of $B$ with $\mathfrak{Q} \subseteq y$, of height $1$, and not containing the image of $\varpi$, the algebra $B$ over `chartAlgInf` $A$ $K_0$ $j_0$ satisfies `Algebra.IsUnramifiedAt` at $\mathfrak{Q}$.
--
--   This is the horizontal half of the local analysis of the pole chart of $X_H(q^2M')$ over the $X_0(M')$ floor at a closed point of the special fibre lying on the $\infty$-branch $W_0$ and at the cusps ($j^{-1} \in y$), in the case $q = 3$, where the covering of the $\infty$-branch degenerates; the primes treated are those not containing the uniformiser. It feeds the verification that the fibre of the localisation of the pole chart at such a point is a regular local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three.lean

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

theorem ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
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
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∉ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) 𝔔 := by sorry
