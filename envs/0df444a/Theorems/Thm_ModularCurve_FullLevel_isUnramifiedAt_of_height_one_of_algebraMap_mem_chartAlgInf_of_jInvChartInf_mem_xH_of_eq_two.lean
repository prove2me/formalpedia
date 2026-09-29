-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two
-- name    : ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/f27dd9b8-e773-58e5-8465-1007001e4563
-- title:
--   Unramifiedness at vertical height-one primes at ∞-chart cusps, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ for which some ring homomorphism $L \to \mathbb{C}$ carries $\zeta$ to $\exp(2\pi i/q)$. Let $K$ be the intermediate field of $\mathrm{LaurentSeries}\ L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image of the function field [`ModularCurve.xHFunctionField (q ^ 2 * M')`](def/ModularCurve_XH.html#L79) at the level subgroup [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, and with a compatible $A$-algebra structure on $K$; let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with underlying Laurent series the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. Let $W_0$ be a valuation subring of $K$ characterised by: $f \in W_0$ exactly when $f \cdot y = x$ in $\mathrm{LaurentSeries}\ L$ for some power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$. Write $A_\infty(K)$ for [`AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L144), the $A$-subalgebra of $K$ of elements integral over $A[j^{-1}]$, and let $X$ be the two-chart integral model, the pushout of the two chart maps, with its structure morphism to $\operatorname{Spec} A$. Let $z$ be a point of $X$ at which the germ of the image of $\varpi$ under the structure morphism lies in the maximal ideal of the stalk, and let $y$ be a point of $\operatorname{Spec} A_\infty(K)$ mapping to $z$ under the canonical morphism and with $\mathfrak p_y$ maximal. Assume $j^{-1}$, as the element `jInvChartInf` of $A_\infty(K)$, lies in $\mathfrak p_y$ (a cusp), and that every $b \in A_\infty(K)$ whose image in $K$ lies in the nonunits of $W_0$ lies in $\mathfrak p_y$. Let $K_0 \le K$ be the base change to $L$ of [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')`](def/ModularCurve_X1.html#L101), equipped with a compatible $A$-algebra structure, let $j_0 \in K_0$ be nonzero with the same underlying Laurent series as $j$, and let $\iota : A_\infty(K_0) \to A_\infty(K)$ be a ring homomorphism compatible with the inclusion $K_0 \hookrightarrow K$, used as the algebra structure. Then for every prime ideal $\mathfrak Q$ of $A_\infty(K)$ with $\mathfrak Q \subseteq \mathfrak p_y$, of height $1$, and containing the image of $\varpi$, the algebra $A_\infty(K_0) \to A_\infty(K)$ is unramified at $\mathfrak Q$ in the sense of `Algebra.IsUnramifiedAt`.
--
--   This is the $q=2$ case of the cusp-side unramifiedness statement for the pole ($j^{-1}$) chart of the two-chart integral model of $X_H(q^2M')$ over $X_0(M')$ along the branch cut out by the valuation subring $W_0$; since for $q=2$ the relevant covering of the $\infty$-branch is trivial, the assertion holds for all vertical height-one primes below the chosen cusp. It feeds the verification that the fibre of the localisation of the pole chart at such a prime is a regular local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two.lean

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

theorem ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two
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
