-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_three
-- name    : ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/91fd4d48-370e-5806-aeb4-8904f7702ba2
-- title:
--   Smoothness of the two-chart model along the Gauss branch, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\ge 1$ with $q\nmid M'$, let $L$ be a field of characteristic zero that is algebraic over $\mathbb{Q}$ and contains a primitive $q$-th root of unity $\zeta$, and assume there is a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\zeta)=e^{2\pi i/q}$. Let $K\subseteq L(\!(X)\!)$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image, under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81), of the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/ModularCurve_XH.html#L79), where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, with perfect residue field and with uniformiser $\varpi$, the $A$-algebra structures on $L$ and $K$ being compatible. Let $j\in K$ be nonzero with Laurent expansion the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal and $f\cdot y=x$ in $L(\!(X)\!)$ after pushing coefficients to $L$. On $\mathfrak{X}=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout glueing $\operatorname{Spec}$ of the integral closure of $A[j]$ in $K$ to $\operatorname{Spec}$ of the integral closure of $A[j^{-1}]$ in $K$, let $z$ be a point at which the germ of $\varpi$ (transported along `toBase`) lies in the maximal ideal of the stalk. Assume: for every point $y$ of either chart lying over $z$, every element of the chart algebra whose image in $K$ is a nonunit of $W_0$ lies in the prime $y$; and, for every point $y$ of the finite chart over $z$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the finite chart algebra to $\Omega$ with kernel $y$, the value $\varphi(j)$ does not lie in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $j\in\Omega$ such that every elliptic Weierstrass curve over $\Omega$ with invariant $j$ has no nontrivial $q$-torsion point. Then there is an open subscheme $U\subseteq\mathfrak{X}$ with $z\in U$ such that the inclusion of $U$ followed by [`AlgebraicCurve.TwoChartIntegralModel.toBase A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) is smooth.
--
--   This is the $q=3$ instance of the smoothness statement for the two-chart integral model of the modular curve of level $\Gamma_H(q^2M')$: the model is smooth over $\operatorname{Spec} A$ near any point of the special fibre lying on the centre of the Gauss valuation $W_0$ (the $\infty$-branch) whose $j$-value is not supersingular in characteristic $q$. It feeds [`ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_three), and thence the construction of the smooth Igusa base model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_three
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
    [PerfectField (IsLocalRing.ResidueField A)]
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

    (hzFin : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)
    (hzInf : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base y = z →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (hord : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω) :
    ∃ U : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).Opens,
      z ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := by sorry
