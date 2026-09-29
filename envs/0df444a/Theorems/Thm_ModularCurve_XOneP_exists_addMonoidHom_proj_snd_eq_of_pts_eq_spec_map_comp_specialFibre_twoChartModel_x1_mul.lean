-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_addMonoidHom_proj_snd_eq_of_pts_eq_spec_map_comp_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_addMonoidHom_proj_snd_eq_of_pts_eq_spec_map_comp_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/ca29abeb-b94f-57c1-8c70-08d01b5b31ad
-- title:
--   Residue-field twists act on J_E through a single additive map
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a characteristic-zero field $L$ that is a $p$-cyclotomic extension of $\mathbb{Q}$, a primitive $p$-th root of unity $\zeta\in L$, and the intermediate field $K$ of $L\subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$; let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$ be nonzero with Laurent expansion the coefficient embedding of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Write $X\to\operatorname{Spec}A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252). Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1:C_1\to\operatorname{Spec}k$, $c_2:C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, equipped with closed immersions $i_1,i_2$ into the base change $X_k=X\times_{\operatorname{Spec}A}\operatorname{Spec}k$ over $k$, whose images together cover $X_k$; assume $C_1\times_{X_k}C_2$ is reduced with $\mathrm{Nat.card}=n>0$. Let $\varepsilon$ be a section of $X\to\operatorname{Spec}A$, and $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base-changed section of $\varepsilon$. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $X\to\operatorname{Spec}A$ (a scheme $P$ with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}A$ and a zero section), assumed to carry a representation of the subfunctor of rigidified line bundles that are fibrewise algebraically trivial, with $D.\mathrm{toBase}$ smooth and separated; let $hreps$ be such a representation for $X_k$ by the base change $D_k=D.\mathrm{baseChange}\,k$, whose Poincaré bundle is isomorphic to the base change of the pullback of the Poincaré bundle of $D$ along the first projection of $D_k$; let $D_1,D_2$ be designations for $c_1,c_2$ with such representations. Let $\nu_2$ be a morphism $D_k.\mathrm{toBase}\to D_2.\mathrm{toBase}$ over $k$ such that for every $k$-scheme $T$ and every $T$-point $a$ of $D_k.\mathrm{toBase}$ the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification along the rigidifying section of the pullback, under the curve-change map attached to $i_2$, of the pullback of the Poincaré bundle of $D_k$ along $a$. Let $G$ be a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), that is abelian groups $J_{0s}$, $J_I$, $J_E$, a subgroup $\mathrm{torus}\le J_{0s}$ and a surjective homomorphism $\mathrm{proj}:J_{0s}\to J_I\times J_E$ with kernel $\mathrm{torus}$, together with bijections $\mathrm{pts},\mathrm{ptsI},\mathrm{ptsE}$ from $J_{0s},J_I,J_E$ onto the $k$-points of $D_k.\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ that turn addition into tensor product of the corresponding pullbacks of the three Poincaré bundles, and such that for every $x\in J_{0s}$ the first component of $\mathrm{proj}(x)$ corresponds under $\mathrm{ptsI}$ to $\mathrm{pts}(x)$ post-composed with the morphism $D_k.\mathrm{toBase}\to D_1.\mathrm{toBase}$ induced by $i_1$, and the second component corresponds under $\mathrm{ptsE}$ to $\mathrm{pts}(x)$ post-composed with $\nu_2$. Finally let $\bar\sigma$ be a surjective ring endomorphism of $k$. Then there exists an additive map $\Phi_E:J_E\to J_E$ such that for all $y,y'\in J_{0s}$: if $\mathrm{pts}(y')$ followed by the projection $P_k\to P$ of $D_k$ equals $\operatorname{Spec}(\bar\sigma)$ followed by $\mathrm{pts}(y)$ followed by that projection, then the second component of $\mathrm{proj}(y')$ equals $\Phi_E$ applied to the second component of $\mathrm{proj}(y)$. No uniqueness of $\Phi_E$ is asserted.
--
--   This is a step in the analysis of the special fibre at $p$ of the Néron model of $J_1(Mp)$, where the fibre of the two-chart integral model splits into a cuspidal component and an étale Igusa component: a twist of a $k$-point by a surjective endomorphism of the residue field is recorded on the étale part $J_E$ by a single additive map. It is used in the treatment of the action of the decomposition subgroup on the relative $\mathrm{Pic}^0$ of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_addMonoidHom_proj_snd_eq_of_pts_eq_spec_map_comp_specialFibre_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_addMonoidHom_proj_snd_eq_of_pts_eq_spec_map_comp_specialFibre_twoChartModel_x1_mul
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

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (σbar : k →+* k)

    (hσbar : Function.Surjective σbar) :
    ∃ ΦE : G.JE →+ G.JE,
      ∀ (y y' : G.J0s),
        (pts y').1 ≫ pullback.fst D.toBase (specMap A k) =
          Spec.map (CommRingCat.ofHom σbar) ≫ (pts y).1 ≫ pullback.fst D.toBase (specMap A k) →
        (G.proj y').2 = ΦE (G.proj y).2 := by sorry
