-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_sections_valuationSubring_extending_and_reduction_eq_of_mem_inertia_of_curveModel_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_sections_valuationSubring_extending_and_reduction_eq_of_mem_inertia_of_curveModel_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/3fa5343a-d47f-5f7c-aba3-27bdf3220ef6
-- title:
--   Inertia translates extend to Pl-sections with equal reduction
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image under the coefficientwise map [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ over $\mathbb{Q}$, let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j\in K$ be the element whose Laurent expansion is [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), assumed non-zero. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and write $X=$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) $\to \operatorname{Spec} A$ for the two-chart model, assumed proper. The following data concerning the special fibre $X\times_A k$ are also assumed: two schemes $C_1,C_2$ proper, smooth of relative dimension $1$ and geometrically integral over $k$, closed immersions $i_1,i_2$ of them into $X\times_A k$ over $k$, the hypothesis that every point of $X\times_A k$ lies in the image of $i_1$ or of $i_2$, that the scheme-theoretic intersection $C_1\times_{X\times_A k}C_2$ is reduced, and a positive integer $n$ equal to the cardinality of its underlying set. Let $\overline{\mathbb{Q}}$ be an $A$- and $L$-algebra compatibly, let $M_\eta$ be a `CurveModel` over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, with a specified isomorphism of that field with its function field, a bijection between closed points and places matching stalks with valuation rings, and every finite set of points contained in an affine open), and let $e_\eta$ be an isomorphism $M_\eta.C\to X\times_A\overline{\mathbb{Q}}$ over $\operatorname{Spec}\overline{\mathbb{Q}}$. Let $Pl\subseteq\overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit of $Pl$, let $\rho:A\to Pl$ be a ring map inducing the structure map $A\to\overline{\mathbb{Q}}$, and let $\pi_k:Pl\to k$ be a surjective ring map with $\pi_k\circ\rho$ the structure map $A\to k$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in the image of the inertia subgroup of $Pl$ inside its decomposition group, acting trivially on the image of $L$, and let $P,P'$ be sections of $M_\eta.\mathrm{toBase}$ such that the point of $X$ determined by $P'$ (through $e_\eta$ and the first projection) is $\operatorname{Spec}\sigma$ followed by the point determined by $P$. Then there exist morphisms $Pt,Pt':\operatorname{Spec} Pl\to X$ over $\operatorname{Spec}\rho$, a morphism $u_\kappa:\operatorname{Spec} k\to X\times_A k$, and a ring endomorphism $\sigma_{Pl}$ of $Pl$ such that the points of $X$ determined by $P$ and $P'$ are the restrictions of $Pt$ and $Pt'$ along $Pl\hookrightarrow\overline{\mathbb{Q}}$; the first projection of $u_\kappa$ equals both $\operatorname{Spec}\pi_k$ followed by $Pt$ and $\operatorname{Spec}\pi_k$ followed by $Pt'$; the second projection of $u_\kappa$ is the identity of $\operatorname{Spec} k$; $\sigma_{Pl}$ is the restriction of $\sigma$ to $Pl$, satisfies $\pi_k\circ\sigma_{Pl}=\pi_k$, and $Pt'=\operatorname{Spec}\sigma_{Pl}$ followed by $Pt$.
--
--   This is the valuative criterion of properness applied to the two-chart model of $X_1(Mp)$ over the ring of integers above $p$ in $\mathbb{Q}(\zeta_p)$: a geometric point and its translate by an element of inertia extend uniquely to sections over the valuation ring $Pl$, and, inertia acting trivially on the residue field, the two sections have the same reduction, recorded as a single $k$-point of the special fibre. It is used in the subsequent analysis of the difference of the two points in the relative Picard group of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_sections_valuationSubring_extending_and_reduction_eq_of_mem_inertia_of_curveModel_twoChartModel_x1_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_sections_valuationSubring_extending_and_reduction_eq_of_mem_inertia_of_curveModel_twoChartModel_x1_mul
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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσI : σ ∈ Pl.inertiaSubgroupIn ℚ)
    (hσL : ∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l)
    (P P' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hP' : P'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
      Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ P.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) :
    ∃ (Pt Pt' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (uκ : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
      (σPl : ↥Pl →+* ↥Pl),
      P.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ Pt.1 ∧
      P'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ Pt'.1 ∧
      uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ Pt.1 ∧
      uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ Pt'.1 ∧
      uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
      Pl.subtype.comp σPl = (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)).comp Pl.subtype ∧
      πk.comp σPl = πk ∧
      Pt'.1 = Spec.map (CommRingCat.ofHom σPl) ≫ Pt.1 := by sorry
