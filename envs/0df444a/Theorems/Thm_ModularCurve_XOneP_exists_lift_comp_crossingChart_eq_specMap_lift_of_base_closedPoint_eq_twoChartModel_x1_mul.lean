-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/d363f1e3-591f-5c5c-b102-043d31f382d3
-- title:
--   Sections through a crossing factor through the crossing chart
-- statement:
--   Fix a prime $p$, a natural number $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ obtained by adjoining to $L$ the image, under the coefficientwise map $\mathtt{coeffEmb}\,L$, of the function field `x1FunctionField (M * p)` inside $\operatorname{LaurentSeries}\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, and let $K$ be an $A$-algebra compatibly with the tower $A \subseteq L \subseteq K$; let $j \in K$ be the element whose Laurent expansion is the image of the $q$-expansion `jq`, assumed nonzero. Let $k$ be an algebraically closed field of characteristic $p$ and an $A$-algebra, and let $\varpi$ generate the maximal ideal of $A$. The geometric data over $k$: two proper, smooth of relative dimension $1$, geometrically integral curves $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$, together with closed immersions $i_1, i_2$ of them, over $\operatorname{Spec} k$, into the base change $X_k := \operatorname{pullback}$ of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) along $\operatorname{Spec} k \to \operatorname{Spec} A$, whose images cover all points of $X_k$, such that the scheme-theoretic intersection $C_1 \times_{X_k} C_2$ is reduced and has exactly $n > 0$ points. Further, $\operatorname{Spec}\mathbb{Q}^{\mathrm{alg}}$-level data: a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $Pl$, a ring map $\rho : A \to Pl$ inducing the given $A$-algebra structure on $\overline{\mathbb{Q}}$, a surjection $\pi_k : Pl \to k$ with $\pi_k \circ \rho$ the structure map $A \to k$, and a morphism $bc$ from $X_k$ to the base change $X_{Pl}$ of the two-chart model along $\operatorname{Spec}(\rho)$ compatible with the first projections and, on the second projections, with $\operatorname{Spec}(\pi_k)$. Finally, let $\nu$ be a point of $C_1 \times_{X_k} C_2$, write $x_\nu$ for its image in $X_{Pl}$ under the first projection followed by $i_1$ followed by $bc$, let $e \in \mathbb{N}$, let $U$ be an open subscheme of $X_{Pl}$ containing $x_\nu$, and let $f : U \to \operatorname{Spec}\bigl(Pl[X_0,X_1]/(X_0X_1 - \rho(\varpi)^e)\bigr)$ be a morphism over $\operatorname{Spec} Pl$ (that is, $f$ followed by the structure morphism agrees with the inclusion $U \hookrightarrow X_{Pl}$ followed by the second projection) whose vertex locus is exactly $x_\nu$: for a point $y$ of $U$, the prime $f(y)$ contains both coordinate classes `CrossingQuotient.U` and `CrossingQuotient.V` if and only if $y$ maps to $x_\nu$. Let $sA : \operatorname{Spec} Pl \to X_{Pl}$ be a section of the second projection sending the closed point of $Pl$ to $x_\nu$. The conclusion: there exist $x', y' \in Pl$ with $x'y' = \rho(\varpi)^e$, both lying in the maximal ideal of $Pl$, and a morphism $sU : \operatorname{Spec} Pl \to U$ with $sU$ followed by $U \hookrightarrow X_{Pl}$ equal to $sA$ and $sU$ followed by $f$ equal to $\operatorname{Spec}$ of the $Pl$-algebra map `CrossingQuotient.lift` determined by sending the two coordinates to $x'$ and $y'$.
--
--   This is the statement that a $Pl$-valued section of the two-chart model of $X_1(Mp)$ whose closed point is a crossing of the reduction lies, in a crossing chart $uv = \rho(\varpi)^e$ around that crossing, at a point of the open annulus: the section extends over the chart neighbourhood (the base being local) and its two chart coordinates are nonunits with product $\rho(\varpi)^e$. It is used in the construction of the invertible pullback and unit identifications at a supersingular crossing of the reduction of the two-chart model of $X_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    (ν : ↥(pullback i₁.1 i₂.1))
    (e : ℕ)
    (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hxU : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal ∧
        CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ↔
      U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν)

    (sA : Spec (CommRingCat.of ↥Pl) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hsA : sA ≫ pullback.snd _ _ = 𝟙 _)
    (hsn : sA.base (IsLocalRing.closedPoint ↥Pl) =
      (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) :
    ∃ (x' y' : ↥Pl) (hxy : x' * y' = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
      (sU : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0})),
      x' ∈ IsLocalRing.maximalIdeal ↥Pl ∧ y' ∈ IsLocalRing.maximalIdeal ↥Pl ∧
      sU ≫ U.ι = sA ∧
      sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e) x' y' hxy).toRingHom) := by sorry
