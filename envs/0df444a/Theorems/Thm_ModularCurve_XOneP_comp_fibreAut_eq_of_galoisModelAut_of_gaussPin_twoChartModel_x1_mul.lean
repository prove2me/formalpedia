-- Prove2me | Theorems.Thm_ModularCurve_XOneP_comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/bcedfedc-8a0a-5e85-b510-d26cf6bf0947
-- title:
--   Galois model automorphism acts trivially on the Gauss component
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$, let $L$ be a field of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$ with $\zeta\in L$ a primitive $p$-th root of unity, and let $K\subseteq L((q))$ be the $L$-subfield `laurentBaseChange L (x1FunctionField (M*p))`, generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with an $A$-algebra structure on $K$ forming a scalar tower over $L$, and let $j\in K$ be nonzero with Laurent expansion the coefficientwise image of $\mathrm{jq}$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1\colon C_1\to\operatorname{Spec}k$, $c_2\colon C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, with closed immersions $i_1,i_2$ of $C_1,C_2$ into the base change along $\operatorname{Spec}k\to\operatorname{Spec}A$ of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), compatible with $c_1,c_2$; assume the images of $i_1,i_2$ cover every point of that base change, that the fibre product of $i_1$ and $i_2$ is reduced, and that its underlying type has cardinality $n>0$. Let $\varepsilon$ be a section of `modelTo` over $\operatorname{Spec}A$, let $\varepsilon_1,\varepsilon_2$ be sections of $c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base change `sectionBaseChange k ε`, and assume `modelTo` is proper. Suppose $\operatorname{Gal}(L/\mathbb{Q})$ acts on $A$ by semiring automorphisms compatibly with $A\to L$. Let $w$ consist of a weight-one modular form on $\Gamma_1(M)$ together with an integral $q$-expansion power series whose reduction `intSeriesC k` is nonzero, let $\mathrm{Mdl}_1$ be a curve model over $k$ (a proper smooth integral curve with a specified isomorphism of its function field with the Igusa field `igusaFunctionFieldX1C k M w`, adjoining to the $q$-expansion field of $\Gamma_1(M)$ over $k$ the inverse of that reduced series, together with a bijection onto the places and matching of stalks) and let $e_1\colon \mathrm{Mdl}_1.C\cong C_1$ satisfy $e_1$ followed by $c_1$ equals $\mathrm{Mdl}_1.\mathrm{toBase}$. Assume the preimage in $\mathrm{Mdl}_1.C$ of the $j$-finite chart `ιFin` under $e_1$ followed by $i_1$ and the first projection is nonempty, and assume the Gauss reading $\mathrm{hgauss}_1$: for every $a$ in `chartAlgFin A K j` and all power series $x,y$ over $A$ with $y$ having nonzero reduction to $k$, if $a\cdot y=x$ in $L((q))$ then the element of the Igusa field obtained by restricting $a$ along that composite, taking the germ at the generic point and transporting by $\mathrm{Mdl}_1.\mathrm{ffEquiv}^{-1}$, has Laurent expansion the quotient of the reductions of $x$ and $y$ in $k((q))$. Let $s\in\operatorname{Gal}(L/\mathbb{Q})$ act trivially on $A$ after reduction to $k$. Let $w_s$ be an automorphism of [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) lying over $\operatorname{Spec}$ of the action of $s$ on $A$, compatible via a ring automorphism $\rho_s$ of `chartAlgFin A K j` acting coefficientwise by $s$ on Laurent expansions (with `ιFin` followed by $w_s$ equal to $\operatorname{Spec}\rho_s$ followed by `ιFin`) and with $\varepsilon$ followed by $w_s$ equal to $\operatorname{Spec}$ of $s$ followed by $\varepsilon$; assume no point of the base-changed section `sectionBaseChange k ε` lies in the image of $i_2$. Finally let $w_k$ be an automorphism of the special fibre with $w_k$ followed by the first projection equal to the first projection followed by $w_s$, and $w_k$ followed by the second projection equal to the second projection. Then $i_1$ followed by $w_k$ equals $i_1$.
--
--   This is the fixing statement for the Galois twist of the two-chart model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$: an automorphism induced by $s\in\operatorname{Gal}(L/\mathbb{Q})$ acting trivially on the residue field restricts to the identity on the component of the special fibre read by $q$-expansions (the Igusa, or Gauss, component). It is used in the subsequent analysis of the Galois action on points of the special fibre and on the associated Abel–Jacobi data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.comp_fibreAut_eq_of_galoisModelAut_of_gaussPin_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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

    (s : L ≃ₐ[ℚ] L) (hsk : ∀ a : A, algebraMap A k (s • a) = algebraMap A k a)

    (ws : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
      ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s : L →+* L) ((b : ↥K) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws.hom = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (hεs : ε.1 ≫ ws.hom = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1)

    (hεC₂ : ∀ t, ((sectionBaseChange k ε).1).base t ∉ Set.range i₂.1.base)

    (wk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hwk₁ : wk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ ws.hom)
    (hwk₂ : wk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :

    i₁.1 ≫ wk.hom = i₁.1 := by sorry
