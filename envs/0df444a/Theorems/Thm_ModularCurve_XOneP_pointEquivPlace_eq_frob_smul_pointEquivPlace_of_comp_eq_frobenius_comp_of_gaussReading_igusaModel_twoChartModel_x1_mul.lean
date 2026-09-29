-- Prove2me | Theorems.Thm_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/b5f8fb00-dd3e-55c0-a0ac-f9fa31d90053
-- title:
--   Frobenius twist of k-points acts by coefficientwise Frobenius on Igusa places
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$; let $L$ be a field of characteristic zero which is a $p$-th cyclotomic extension of $\mathbb{Q}$, with $\zeta \in L$ a primitive $p$-th root of unity, and let $K$ be the intermediate field of $L(\!(q)\!)$ over $L$ obtained by adjoining to $L$ the coefficientwise image of the function field `x1FunctionField (M * p)` of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $L$; let $j \in K$ be the element whose Laurent series is the coefficientwise image of the $q$-expansion `jq`, assumed nonzero. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. Two proper, geometrically integral $k$-schemes $C_1, C_2$, smooth of relative dimension $1$ over $\operatorname{Spec} k$, are given together with closed immersions $i_1, i_2$ into the base change along $\operatorname{Spec} k \to \operatorname{Spec} A$ of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), commuting with the structure morphisms; the images of $i_1$ and $i_2$ are assumed to cover that base change, their scheme-theoretic intersection $\operatorname{pullback} i_1 \, i_2$ is assumed reduced with cardinality $n > 0$. Let $w$ be an integral weight-one form of level $M$ over $k$, that is, a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion whose image in $k(\!(q)\!)$ is nonzero; let $\mathrm{Ig} =$ `igusaFunctionFieldX1C k M w` be the subfield of $k(\!(q)\!)$ generated over the level-$M$ $q$-expansion field by the inverse of that image. Let $\mathrm{Mdl}_1$ be a curve model over $k$ with function field identified with $\mathrm{Ig}$, and $e_1 : \mathrm{Mdl}_1.C \cong C_1$ an isomorphism with $e_1$ followed by $c_1$ equal to the structure morphism of the model; the preimage in $\mathrm{Mdl}_1.C$ of the finite chart of the two-chart model under $e_1$ followed by $i_1$ followed by the first projection is assumed nonempty, and the identification is pinned by a $q$-expansion condition: for $a$ in the $A$-subalgebra of elements of $K$ integral over $A[j]$ and power series $x, y$ over $A$ with $\bar{y} \ne 0$ and $a\,y = x$ in $L(\!(q)\!)$, the germ of the pullback of $a$ at the generic point, read in $\mathrm{Ig}$, has Laurent series $\bar{x}/\bar{y}$. Finally let $\mathrm{frobIg}$ be a semilinear automorphism of $\mathrm{Ig}$ over $k$ (a pair of ring automorphisms of $\mathrm{Ig}$ and of $k$ compatible with the structure map) acting on every Laurent coefficient by $t \mapsto t^p$. The conclusion: for all sections $c, c'$ of $c_1$, if $c'$ followed by $i_1$ followed by the projection to the two-chart model equals $\operatorname{Spec}$ of the $p$-power Frobenius of $k$ followed by $c$ followed by $i_1$ followed by that projection, then the place of $\mathrm{Ig}$ over $k$ attached by $\mathrm{Mdl}_1.\mathrm{pointEquivPlace}$ to $c'$ transported through $e_1^{-1}$ equals $\mathrm{frobIg}$ applied to the place attached to $c$.
--
--   This identifies, on the component of the special fibre of the two-chart model of $X_1(Mp)$ at $p$ whose function field is the Igusa field, the effect of twisting a $k$-point by the arithmetic Frobenius of $k$: on places of the Igusa field it is the coefficientwise $p$-th power map on $q$-expansions. It is used in the subsequent computation of the reduction of Hecke divisors on that component as a Frobenius translate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul
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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p) :
    ∀ (c c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      c'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (frobenius k p)) ≫ c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) →
      Mdl₁.pointEquivPlace ⟨c'.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c'.2⟩ =
        frobIg • Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩ := by sorry
