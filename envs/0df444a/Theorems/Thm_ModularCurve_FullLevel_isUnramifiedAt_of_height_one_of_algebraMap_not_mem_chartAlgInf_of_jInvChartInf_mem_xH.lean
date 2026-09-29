-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH
-- name    : ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/f45f533b-06ab-532e-85d1-7b3298fc96fe
-- title:
--   Unramifiedness at horizontal height-one primes below an ∞-cusp
-- statement:
--   Fix a prime $q\ge 5$ and a natural number $M'\neq 0$ with $q\nmid M'$; let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$, and assume there is a ring homomorphism $L\to\mathbb{C}$ carrying $\zeta$ to $\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L(\!(t)\!)$ generated over $L$ by the coefficientwise image of the function field of $X_H$ at level $q^2M'$, $H$ the kernel of $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, and let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly, and with uniformiser $\varpi$ generating the maximal ideal. Let $j\in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), and let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which $f\,y=x$ in $L(\!(t)\!)$ for some power series $x,y$ over $A$ with $y$ nonzero modulo the maximal ideal. Let $z$ be a point of the two-chart integral model over $A$, namely the pushout of the two $\mathrm{Spec}$-maps attached to the integral closures $A_{\mathrm{fin}}$ of $A[j]$ and $A_\infty$ of $A[j^{-1}]$ in $K$, such that the germ at $z$ of the global section obtained from $\varpi$ along the structure map to $\mathrm{Spec}\,A$ lies in the maximal ideal of the stalk; let $y$ be a maximal prime of $A_\infty=$ `chartAlgInf A K j` mapping to $z$ under the $\infty$-chart immersion, with $j^{-1}\in y$, and such that every element of $A_\infty$ whose image in $K$ is a nonunit of $W_0$ lies in $y$. Let $K_0\le K$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion field of $\Gamma_0(M')$, with compatible $A$-action and with $j_0\in K_0$ nonzero having the same expansion, and let $\iota$ be a ring homomorphism `chartAlgInf A K₀ j₀` $\to$ `chartAlgInf A K j` inducing the inclusion $K_0\hookrightarrow K$; regard $A_\infty$ as an algebra over the floor chart via $\iota$. Then for every prime $\mathfrak{Q}$ of $A_\infty$ with $\mathfrak{Q}\subseteq y$, of height $1$, and not containing the image of $\varpi$, the algebra $A_\infty$ over `chartAlgInf A K₀ j₀` is unramified at $\mathfrak{Q}$.
--
--   This is the horizontal ($\varpi\notin\mathfrak{Q}$) case of the local analysis of the $\infty$-chart of the integral model of $X_H(q^2M')$ over the $X_0(M')$-floor at a cusp of the branch determined by $W_0$; such $\mathfrak{Q}$ is the centre of a place of $K/L$ specialising to $y$, and the ramification index over the floor is computed there to be $1$. It feeds, together with the companion statement for primes containing $\varpi$, into the proof that the fibre of the localisation of the $\infty$-chart at the prime below a cusp is a regular local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH.lean

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

theorem ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
